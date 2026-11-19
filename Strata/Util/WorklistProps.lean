/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Util.Worklist
import all Strata.Util.Worklist
import all Init.Data.Queue
import Strata.Util.StateMProps
import Std.Data.HashSet.Lemmas

/-! # Properties of the generic worklist algorithm

What a run of `Strata.Worklist.run` computes, for a `process` step in `StateM`: the invariants
it keeps, and that a drained run has processed every seed and every successor once.

## Key results

- `run_inv`, `run_items_inv` — the driver keeps any invariant every processing step keeps.
- `run_dedup` — no two equal items are processed.
- `run_complete` — a drained run has processed every seed.
- `run_closed` — a drained run has processed every successor of every marked item.
-/

namespace Strata.Worklist

public section

variable {σ α β : Type}

/-- One worklist iteration keeps an invariant of the state that every processing step keeps. -/
private theorem runOneIter_inv [BEq α] [Hashable α] (Inv : σ → Prop)
    (process : α → StateM σ (List α)) (hp : ∀ a s, Inv s → Inv ((process a).run s).2)
    (st : Std.Queue α × Std.HashSet α) (s : σ) (hs : Inv s) :
    Inv ((Strata.Worklist.runOneIter process st).run s).2 := by
  unfold Strata.Worklist.runOneIter
  simp only [StateT.run, bind]
  rcases hq : st.fst.dequeue? with _ | ⟨a, pending⟩
  · exact hs
  · simp only [StateT.bind]
    have h1 := hp a s hs
    simp only [StateT.run] at h1
    generalize process _ s = r at h1 ⊢
    obtain ⟨news, s1⟩ := r
    show Inv ((List.foldlM _ (pending, st.snd) news : StateM σ _) s1).2
    refine foldlM_state_inv Inv news _ ?_ _ s1 h1
    intro a _ b s hs
    split <;> exact hs

/-- The worklist driver keeps an invariant of the state that every processing step keeps. -/
theorem run_inv [BEq α] [Hashable α] (Inv : σ → Prop) (process : α → StateM σ (List α))
    (hp : ∀ a s, Inv s → Inv ((process a).run s).2) (initial : List α) (cap : Nat) (s : σ)
    (hs : Inv s) : Inv ((Strata.Worklist.run initial process cap).run s).2 := by
  unfold Strata.Worklist.run
  simp only [StateT.run, bind, StateT.bind]
  split
  rename_i r a s' heq
  have h1 : Inv s' := forIn_state_inv_of_eq Inv heq
    (fun a _ b s hs => by split <;> exact hs) hs
  have hit : ∀ n st s, Inv s → Inv ((Strata.Worklist.runIterations process n st).run s).2 := by
    intro n
    induction n with
    | zero => intro st s hs; exact hs
    | succ n ih =>
      intro st s hs
      unfold Strata.Worklist.runIterations
      simp only [StateT.run, bind, StateT.bind]
      have h2 := runOneIter_inv Inv process hp st s hs
      simp only [StateT.run] at h2
      generalize Strata.Worklist.runOneIter process st s = r at h2 ⊢
      obtain ⟨o, s2⟩ := r
      cases o with
      | none => exact h2
      | some st' => exact ih st' s2 h2
  exact hit cap _ s' h1

/-- Every item of a queue satisfies `Q`. -/
def QueueAll (Q : α → Prop) (q : Std.Queue α) : Prop := ∀ a ∈ q.eList ++ q.dList, Q a

/-- Dequeuing from a queue whose items satisfy `Q` gives an item satisfying `Q` and a queue whose
    items do. -/
private theorem QueueAll.dequeue? {Q : α → Prop} {q : Std.Queue α} (hq : QueueAll Q q) {a : α}
    {q' : Std.Queue α} (h : q.dequeue? = some (a, q')) : Q a ∧ QueueAll Q q' := by
  unfold Std.Queue.dequeue? at h
  split at h
  · rename_i d ds hd
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨hq _ (by simp [hd]), fun b hb => hq b ?_⟩
    simp only [List.mem_append] at hb ⊢
    rcases hb with hb | hb
    · exact .inl hb
    · exact .inr (by rw [hd]; exact List.mem_cons_of_mem _ hb)
  · rename_i hd
    split at h
    · cases h
    · rename_i d ds hr
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hmem : ∀ x ∈ d :: ds, x ∈ q.eList := fun x hx => by
        rw [← List.mem_reverse, hr]; exact hx
      refine ⟨hq _ (List.mem_append_left _ (hmem d List.mem_cons_self)), fun b hb => ?_⟩
      simp only [List.nil_append] at hb
      exact hq b (List.mem_append_left _ (hmem b (List.mem_cons_of_mem _ hb)))

/-- Enqueuing an item satisfying `Q` keeps every item of the queue satisfying `Q`. -/
private theorem QueueAll.enqueue {Q : α → Prop} {q : Std.Queue α} (hq : QueueAll Q q) {a : α}
    (ha : Q a) : QueueAll Q (q.enqueue a) := by
  intro b hb
  simp only [Std.Queue.enqueue, List.cons_append, List.mem_cons] at hb
  rcases hb with rfl | hb
  · exact ha
  · exact hq b hb

/-- One worklist iteration keeps an invariant of the state and that every queued item satisfies
    `Q`, when processing an item satisfying `Q` keeps the invariant and discovers items
    satisfying `Q`. -/
private theorem runOneIter_items_inv [BEq α] [Hashable α] (Q : α → Prop) (Inv : σ → Prop)
    (process : α → StateM σ (List α))
    (hp : ∀ a s, Q a → Inv s → Inv ((process a).run s).2 ∧ ∀ b ∈ ((process a).run s).1, Q b)
    (st : Std.Queue α × Std.HashSet α) (hq : QueueAll Q st.1) (s : σ) (hs : Inv s) :
    Inv ((Strata.Worklist.runOneIter process st).run s).2 ∧
      ∀ st' ∈ ((Strata.Worklist.runOneIter process st).run s).1, QueueAll Q st'.1 := by
  unfold Strata.Worklist.runOneIter
  simp only [StateT.run, bind]
  rcases hdq : st.fst.dequeue? with _ | ⟨a, pending⟩
  · exact ⟨hs, by simp [pure, StateT.pure]⟩
  · obtain ⟨hqa, hqp⟩ := hq.dequeue? hdq
    simp only [StateT.bind]
    have h1 := hp a s hqa hs
    simp only [StateT.run] at h1
    generalize process _ s = r at h1 ⊢
    obtain ⟨news, s1⟩ := r
    simp only at h1
    refine ⟨?_, ?_⟩
    · show Inv ((List.foldlM _ (pending, st.snd) news : StateM σ _) s1).2
      refine foldlM_state_inv Inv news _ ?_ _ s1 h1.1
      intro a _ b s hs
      split <;> exact hs
    · have hacc := foldlM_acc_inv (fun (x : Std.Queue α × Std.HashSet α) => QueueAll Q x.1) news
        (fun (x : Std.Queue α × Std.HashSet α) (b : α) =>
          if x.snd.contains b = true then (pure (x.fst, x.snd) : StateM σ _)
          else pure (Std.Queue.enqueue b x.fst, x.snd.insert b))
        (fun b hb x s hx => by
          split
          · exact hx
          · exact hx.enqueue (h1.2 b hb)) (pending, st.snd) s1 hqp
      simp only [StateT.run] at hacc
      intro st' hst'
      have hst2 : st' ∈ some ((List.foldlM
          (fun (x : Std.Queue α × Std.HashSet α) b =>
            if x.snd.contains b = true then (pure (x.fst, x.snd) : StateM σ _)
            else pure (Std.Queue.enqueue b x.fst, x.snd.insert b))
          (pending, st.snd) news s1).fst) := hst'
      simp only [Option.mem_def, Option.some.injEq] at hst2
      subst hst2
      exact hacc

/-- **The worklist driver keeps an invariant of the state** that every processing step keeps
    on items satisfying `Q`, when the initial items satisfy `Q` and every item a step
    discovers does too. -/
theorem run_items_inv [BEq α] [Hashable α] (Q : α → Prop) (Inv : σ → Prop)
    (process : α → StateM σ (List α))
    (hp : ∀ a s, Q a → Inv s → Inv ((process a).run s).2 ∧ ∀ b ∈ ((process a).run s).1, Q b)
    (initial : List α) (hinit : ∀ a ∈ initial, Q a) (cap : Nat) (s : σ) (hs : Inv s) :
    Inv ((Strata.Worklist.run initial process cap).run s).2 := by
  unfold Strata.Worklist.run
  simp only [StateT.run, bind, StateT.bind]
  split
  rename_i r a s' heq
  have h1 : Inv s' := forIn_state_inv_of_eq Inv heq
    (fun a _ b s hs => by split <;> exact hs) hs
  have hq0 : QueueAll Q a.2 := by
    have hq := forIn_acc_inv (fun (x : Std.HashSet α × Std.Queue α) => QueueAll Q x.2) initial
      (fun (a : α) (x : Std.HashSet α × Std.Queue α) =>
        if (!x.fst.contains a) = true then
          (pure (ForInStep.yield (x.fst.insert a, Std.Queue.enqueue a x.snd)) : StateM σ _)
        else pure (ForInStep.yield (x.fst, x.snd)))
      (fun b hb x s hx => by
        split
        · exact ⟨_, rfl, hx.enqueue (hinit b hb)⟩
        · exact ⟨_, rfl, hx⟩) (∅, ∅) s (fun b hb => by
          simp only [List.mem_append] at hb
          rcases hb with hb | hb <;> cases hb)
    simp only [StateT.run] at hq
    rw [heq] at hq
    exact hq
  have hit : ∀ n st s, QueueAll Q st.1 → Inv s →
      Inv ((Strata.Worklist.runIterations process n st).run s).2 := by
    intro n
    induction n with
    | zero => intro st s _ hs; exact hs
    | succ n ih =>
      intro st s hq hs
      unfold Strata.Worklist.runIterations
      simp only [StateT.run, bind, StateT.bind]
      have h2 := runOneIter_items_inv Q Inv process hp st hq s hs
      simp only [StateT.run] at h2
      generalize Strata.Worklist.runOneIter process st s = r at h2 ⊢
      obtain ⟨o, s2⟩ := r
      cases o with
      | none => exact h2.1
      | some st' => exact ih st' s2 (h2.2 st' rfl) h2.1
  exact hit cap _ s' hq0 h1

/-- The items of a queue, in the order `dequeue?` yields them. -/
def qlist (q : Std.Queue α) : List α := q.dList ++ q.eList.reverse

/-- Dequeuing yields the first item of the queue's list, and leaves the rest. -/
private theorem qlist_dequeue? {q q' : Std.Queue α} {a : α} (h : q.dequeue? = some (a, q')) :
    qlist q = a :: qlist q' := by
  unfold Std.Queue.dequeue? at h
  split at h
  · rename_i d ds hd
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [qlist, hd]
  · rename_i hd
    split at h
    · cases h
    · rename_i d ds hr
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [qlist, hd, hr]

/-- Enqueuing appends to the queue's list. -/
private theorem qlist_enqueue (q : Std.Queue α) (b : α) : qlist (q.enqueue b) = qlist q ++ [b] := by
  simp [qlist, Std.Queue.enqueue]

/-- What the worklist keeps for deduplication: the items processed, `P`, then those queued
    are pairwise distinct and all seen, and the items `proj` records are among those
    processed, in order. -/
def DedupInv [BEq α] [Hashable α] (proj : σ → List α) (P : List α) (Q : Std.Queue α)
    (S : Std.HashSet α) (s : σ) : Prop :=
  (P ++ qlist Q).Pairwise (fun x y => (x == y) = false) ∧
    (∀ x ∈ P ++ qlist Q, S.contains x = true) ∧ (proj s).Sublist P

/-- Queuing an item that has not been seen, and marking it seen, keeps `DedupInv`. -/
private theorem DedupInv.enqueue [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {proj : σ → List α} {P : List α} {Q : Std.Queue α} {S : Std.HashSet α} {s : σ}
    (h : DedupInv proj P Q S s) {b : α} (hb : S.contains b = false) :
    DedupInv proj P (Q.enqueue b) (S.insert b) s := by
  obtain ⟨hp, hc, hs⟩ := h
  rw [DedupInv, qlist_enqueue, ← List.append_assoc]
  refine ⟨List.pairwise_append.mpr ⟨hp, by simp, ?_⟩, ?_, hs⟩
  · intro x hx y hy
    simp only [List.mem_singleton] at hy
    subst hy
    cases hxy : (x == y)
    · rfl
    · have := Std.HashSet.contains_congr (m := S) hxy
      rw [hc x hx, hb] at this; cases this
  · intro x hx
    rw [Std.HashSet.contains_insert]
    rcases List.mem_append.mp hx with hx | hx
    · rw [hc x hx]; simp
    · simp only [List.mem_singleton] at hx; subst hx; simp

/-- One worklist iteration either finds the queue empty and changes nothing, or keeps
    `DedupInv` with the item it processed added. -/
private theorem runOneIter_dedup [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (proj : σ → List α) (process : α → StateM σ (List α))
    (hp : ∀ a s, proj ((process a).run s).2 = proj s ∨ proj ((process a).run s).2 = proj s ++ [a])
    (st : Std.Queue α × Std.HashSet α) (s : σ) (P : List α) (h : DedupInv proj P st.1 st.2 s) :
    (((Strata.Worklist.runOneIter process st).run s).1 = none ∧
        ((Strata.Worklist.runOneIter process st).run s).2 = s) ∨
      ∃ a st', ((Strata.Worklist.runOneIter process st).run s).1 = some st' ∧
        DedupInv proj (P ++ [a]) st'.1 st'.2 ((Strata.Worklist.runOneIter process st).run s).2 := by
  unfold Strata.Worklist.runOneIter
  simp only [StateT.run, bind]
  rcases hdq : st.fst.dequeue? with _ | ⟨a, pending⟩
  · exact .inl ⟨rfl, rfl⟩
  · simp only [StateT.bind]
    have hql := qlist_dequeue? hdq
    have h1 : DedupInv proj (P ++ [a]) pending st.2 s := by
      obtain ⟨hpw, hc, hsub⟩ := h
      rw [hql] at hpw hc
      exact ⟨by simpa using hpw, by simpa using hc, hsub.trans (List.sublist_append_left _ _)⟩
    have hpa := hp a s
    simp only [StateT.run] at hpa
    generalize process a s = r at hpa ⊢
    obtain ⟨news, s1⟩ := r
    simp only at hpa
    have h2 : DedupInv proj (P ++ [a]) pending st.2 s1 := by
      refine ⟨h1.1, h1.2.1, ?_⟩
      rcases hpa with hpa | hpa
      · rw [hpa]; exact h1.2.2
      · rw [hpa]; exact h.2.2.append (List.Sublist.refl _)
    have hfold := foldlM_acc_inv (fun (x : Std.Queue α × Std.HashSet α) =>
        DedupInv proj (P ++ [a]) x.1 x.2 s1) news
      (fun (x : Std.Queue α × Std.HashSet α) (b : α) =>
        if x.snd.contains b = true then (pure (x.fst, x.snd) : StateM σ _)
        else pure (Std.Queue.enqueue b x.fst, x.snd.insert b))
      (fun b _ x _ hx => by
        split
        · exact hx
        · rename_i hc
          exact hx.enqueue (by simpa using hc)) (pending, st.snd) s1 h2
    have hst := foldlM_state_inv (· = s1) news
      (fun (x : Std.Queue α × Std.HashSet α) (b : α) =>
        if x.snd.contains b = true then (pure (x.fst, x.snd) : StateM σ _)
        else pure (Std.Queue.enqueue b x.fst, x.snd.insert b))
      (fun b _ x s hs => by split <;> exact hs) (pending, st.snd) s1 rfl
    simp only [StateT.run] at hfold hst
    refine .inr ⟨a, _, rfl, ?_⟩
    show DedupInv proj (P ++ [a]) _ _ ((List.foldlM _ (pending, st.snd) news : StateM σ _) s1).2
    rw [hst]
    exact hfold

/-- **The worklist processes no two equal items**, so it records no item twice in a state
    whose recorded list `proj` grows by at most the item each step processes. -/
theorem run_dedup [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (proj : σ → List α) (process : α → StateM σ (List α))
    (hp : ∀ a s, proj ((process a).run s).2 = proj s ∨ proj ((process a).run s).2 = proj s ++ [a])
    (initial : List α) (cap : Nat) (s : σ) (hs : proj s = []) :
    (proj ((Strata.Worklist.run initial process cap).run s).2).Pairwise
      (fun x y => (x == y) = false) := by
  unfold Strata.Worklist.run
  simp only [StateT.run, bind, StateT.bind]
  split
  rename_i r a s' heq
  have hs' : s' = s := forIn_state_inv_of_eq (· = s) heq
    (fun a _ b s hs => by split <;> exact hs) rfl
  subst hs'
  have h0 : DedupInv proj [] a.2 a.1 s' := by
    have hd := forIn_acc_inv (fun (x : Std.HashSet α × Std.Queue α) => DedupInv proj [] x.2 x.1 s')
      initial
      (fun (a : α) (x : Std.HashSet α × Std.Queue α) =>
        if (!x.fst.contains a) = true then
          (pure (ForInStep.yield (x.fst.insert a, Std.Queue.enqueue a x.snd)) : StateM σ _)
        else pure (ForInStep.yield (x.fst, x.snd)))
      (fun b _ x _ hx => by
        split
        · rename_i hc
          exact ⟨_, rfl, hx.enqueue (by simpa using hc)⟩
        · exact ⟨_, rfl, hx⟩) (∅, ∅) s'
      ⟨List.Pairwise.nil, fun x hx => absurd hx List.not_mem_nil, by rw [hs]; exact .slnil⟩
    simp only [StateT.run] at hd
    rw [heq] at hd
    exact hd
  have hit : ∀ n (st : Std.Queue α × Std.HashSet α) s P, DedupInv proj P st.1 st.2 s →
      (proj ((Strata.Worklist.runIterations process n st).run s).2).Pairwise
        (fun x y => (x == y) = false) := by
    intro n
    induction n with
    | zero =>
      intro st s P h
      exact ((List.pairwise_append.mp h.1).1).sublist h.2.2
    | succ n ih =>
      intro st s P h
      unfold Strata.Worklist.runIterations
      simp only [StateT.run, bind, StateT.bind]
      have h2 := runOneIter_dedup proj process hp st s P h
      simp only [StateT.run] at h2
      generalize Strata.Worklist.runOneIter process st s = r at h2 ⊢
      obtain ⟨o, s2⟩ := r
      rcases h2 with ⟨ho, hs2⟩ | ⟨a, st', ho, hd⟩
      · simp only at ho hs2
        subst ho hs2
        exact ((List.pairwise_append.mp h.1).1).sublist h.2.2
      · simp only at ho hd
        subst ho
        exact ih st' s2 (P ++ [a]) hd
  exact hit cap (a.2, a.1) s' [] h0

/-! #### Completeness: a drained run has processed every seed -/

/-- A queue `dequeue?` finds empty has no items. -/
private theorem qlist_of_dequeue?_none {q : Std.Queue α} (h : q.dequeue? = none) : qlist q = [] :=
    by
  unfold Std.Queue.dequeue? at h
  split at h
  · cases h
  · rename_i hd
    split at h
    · rename_i hr
      simp [qlist, hd, List.reverse_eq_nil_iff.mp hr]
    · cases h

/-- An empty queue has no items. -/
private theorem qlist_of_isEmpty {q : Std.Queue α} (h : q.isEmpty = true) : qlist q = [] := by
  simp only [Std.Queue.isEmpty, Bool.and_eq_true, List.isEmpty_iff] at h
  simp [qlist, h.1, h.2]

/-- What completeness rests on: every item seen is done, or equal to one still queued. -/
def CompleteInv [BEq α] [Hashable α] (Done : σ → α → Prop) (Q : Std.Queue α)
    (S : Std.HashSet α) (s : σ) : Prop :=
  ∀ x, S.contains x = true → Done s x ∨ ∃ y ∈ qlist Q, (x == y) = true

/-- Enqueuing an item and marking it seen keeps the completeness invariant: every seen item
    is still done or equal to one still queued. -/
private theorem CompleteInv.enqueue [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {Done : σ → α → Prop} {Q : Std.Queue α} {S : Std.HashSet α} {s : σ}
    (h : CompleteInv Done Q S s) (b : α) :
    CompleteInv Done (Q.enqueue b) (S.insert b) s := by
  intro x hx
  rw [Std.HashSet.contains_insert] at hx
  rw [qlist_enqueue]
  rcases Bool.or_eq_true _ _ ▸ hx with hx | hx
  · exact .inr ⟨b, by simp, BEq.symm hx⟩
  · rcases h x hx with h | ⟨y, hy, hxy⟩
    · exact .inl h
    · exact .inr ⟨y, List.mem_append_left _ hy, hxy⟩

/-- One iteration either finds the queue empty, changing nothing, or keeps `CompleteInv`, when
    processing an item makes it done and keeps done items done. -/
private theorem runOneIter_complete [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (Done : σ → α → Prop) (process : α → StateM σ (List α))
    (hmono : ∀ a s x, Done s x → Done ((process a).run s).2 x)
    (hdone : ∀ a s, Done ((process a).run s).2 a)
    (hbeq : ∀ s x y, (x == y) = true → Done s y → Done s x)
    (st : Std.Queue α × Std.HashSet α) (s : σ) (h : CompleteInv Done st.1 st.2 s) :
    (((Strata.Worklist.runOneIter process st).run s).1 = none ∧
        ((Strata.Worklist.runOneIter process st).run s).2 = s ∧ qlist st.1 = []) ∨
      ∃ st', ((Strata.Worklist.runOneIter process st).run s).1 = some st' ∧
        CompleteInv Done st'.1 st'.2 ((Strata.Worklist.runOneIter process st).run s).2 ∧
        ∀ x, st.2.contains x = true → st'.2.contains x = true := by
  unfold Strata.Worklist.runOneIter
  simp only [StateT.run, bind]
  rcases hdq : st.fst.dequeue? with _ | ⟨a, pending⟩
  · exact .inl ⟨rfl, rfl, qlist_of_dequeue?_none hdq⟩
  · simp only [StateT.bind]
    have hql := qlist_dequeue? hdq
    have hd := hdone a s
    have hm := hmono a s
    simp only [StateT.run] at hd hm
    generalize process a s = r at hd hm ⊢
    obtain ⟨news, s1⟩ := r
    simp only at hd hm
    have h2 : CompleteInv Done pending st.2 s1 := by
      intro x hx
      rcases h x hx with hx | ⟨y, hy, hxy⟩
      · exact .inl (hm x hx)
      · rw [hql] at hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact .inl (hbeq s1 x y hxy hd)
        · exact .inr ⟨y, hy, hxy⟩
    have hfold := foldlM_acc_inv (fun (x : Std.Queue α × Std.HashSet α) =>
        CompleteInv Done x.1 x.2 s1 ∧ ∀ y, st.2.contains y = true → x.2.contains y = true) news
      (fun (x : Std.Queue α × Std.HashSet α) (b : α) =>
        if x.snd.contains b = true then (pure (x.fst, x.snd) : StateM σ _)
        else pure (Std.Queue.enqueue b x.fst, x.snd.insert b))
      (fun b _ x _ hx => by
        split
        · exact hx
        · refine ⟨hx.1.enqueue b, fun y hy => ?_⟩
          show (x.snd.insert b).contains y = true
          rw [Std.HashSet.contains_insert, hx.2 y hy, Bool.or_true]) (pending, st.snd) s1
      ⟨h2, fun _ hy => hy⟩
    have hst := foldlM_state_inv (· = s1) news
      (fun (x : Std.Queue α × Std.HashSet α) (b : α) =>
        if x.snd.contains b = true then (pure (x.fst, x.snd) : StateM σ _)
        else pure (Std.Queue.enqueue b x.fst, x.snd.insert b))
      (fun b _ x s hs => by split <;> exact hs) (pending, st.snd) s1 rfl
    simp only [StateT.run] at hfold hst
    refine .inr ⟨_, rfl, ?_⟩
    dsimp only [pure, StateT.pure, bind, StateT.bind] at hfold hst ⊢
    generalize (List.foldlM _ (pending, st.snd) news : StateM σ _) s1 = r at hfold hst ⊢
    obtain ⟨⟨q', S'⟩, s'⟩ := r
    simp only at hfold hst ⊢
    subst hst
    exact hfold

/-- Iterating keeps `CompleteInv`, and when it reports the worklist drained, every seen item is
    done. -/
private theorem runIterations_complete [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (Done : σ → α → Prop) (process : α → StateM σ (List α))
    (hmono : ∀ a s x, Done s x → Done ((process a).run s).2 x)
    (hdone : ∀ a s, Done ((process a).run s).2 a)
    (hbeq : ∀ s x y, (x == y) = true → Done s y → Done s x) :
    ∀ n (st : Std.Queue α × Std.HashSet α) s, CompleteInv Done st.1 st.2 s →
      ((Strata.Worklist.runIterations process n st).run s).1 = true →
      ∀ x, st.2.contains x = true → Done ((Strata.Worklist.runIterations process n st).run s).2 x
  | 0, st, s, h, hfin, x, hx => by
    obtain ⟨pending, seen⟩ := st
    unfold Strata.Worklist.runIterations at hfin ⊢
    have hq := qlist_of_isEmpty hfin
    rcases h x hx with h | ⟨y, hy, -⟩
    · exact h
    · rw [hq] at hy; cases hy
  | n + 1, st, s, h, hfin, x, hx => by
    unfold Strata.Worklist.runIterations at hfin ⊢
    simp only [StateT.run, bind, StateT.bind] at hfin ⊢
    have h2 := runOneIter_complete Done process hmono hdone hbeq st s h
    simp only [StateT.run] at h2
    generalize Strata.Worklist.runOneIter process st s = r at h2 hfin ⊢
    obtain ⟨o, s2⟩ := r
    rcases h2 with ⟨ho, hs2, hq⟩ | ⟨st', ho, hd⟩
    · simp only at ho hs2
      subst ho hs2
      rcases h x hx with h | ⟨y, hy, -⟩
      · exact h
      · rw [hq] at hy; cases hy
    · simp only at ho hd
      subst ho
      exact runIterations_complete Done process hmono hdone hbeq n st' s2 hd.1 hfin x (hd.2 x hx)

/-- The body of `Strata.Worklist.run`'s seeding loop. -/
private abbrev seedStep [BEq α] [Hashable α] (a : α) (x : Std.HashSet α × Std.Queue α) :
    StateM σ (ForInStep (Std.HashSet α × Std.Queue α)) :=
  if (!x.fst.contains a) = true then pure (ForInStep.yield (x.fst.insert a, Std.Queue.enqueue a
      x.snd))
  else pure (ForInStep.yield (x.fst, x.snd))

/-- Seeding keeps `CompleteInv`, keeps what was seen, and sees every seed. -/
private theorem forIn_seed [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (Done : σ → α →
    Prop)
    (s0 : σ) : ∀ (l : List α) (b : Std.HashSet α × Std.Queue α) (s : σ),
      CompleteInv Done b.2 b.1 s0 →
      CompleteInv Done ((forIn l b seedStep).run s).1.2 ((forIn l b seedStep).run s).1.1 s0 ∧
      (∀ x, b.1.contains x = true → ((forIn l b seedStep).run s).1.1.contains x = true) ∧
      (∀ a ∈ l, ((forIn l b seedStep).run s).1.1.contains a = true) ∧
      ((forIn l b seedStep).run s).2 = s
  | [], b, s, h => ⟨h, fun _ hx => hx, fun _ ha => absurd ha List.not_mem_nil, rfl⟩
  | a :: l, b, s, h => by
    have key : ∀ b' : Std.HashSet α × Std.Queue α, CompleteInv Done b'.2 b'.1 s0 →
        (∀ x, b.1.contains x = true → b'.1.contains x = true) → b'.1.contains a = true →
        ((forIn (a :: l) b seedStep).run s) = ((forIn l b' seedStep).run s) →
        CompleteInv Done ((forIn (a :: l) b seedStep).run s).1.2
            ((forIn (a :: l) b seedStep).run s).1.1 s0 ∧
          (∀ x, b.1.contains x = true →
            ((forIn (a :: l) b seedStep).run s).1.1.contains x = true) ∧
          (∀ a' ∈ a :: l, ((forIn (a :: l) b seedStep).run s).1.1.contains a' = true) ∧
          ((forIn (a :: l) b seedStep).run s).2 = s := by
      intro b' hb' hsub ha heq
      rw [heq]
      obtain ⟨h1, h2, h3, h4⟩ := forIn_seed Done s0 l b' s hb'
      refine ⟨h1, fun x hx => h2 x (hsub x hx), fun a' ha' => ?_, h4⟩
      rcases List.mem_cons.mp ha' with rfl | ha'
      · exact h2 _ ha
      · exact h3 a' ha'
    by_cases hc : b.1.contains a = true
    · refine key b h (fun _ hx => hx) hc ?_
      simp [List.forIn_cons, StateT.run, seedStep, hc, bind, StateT.bind, pure, StateT.pure]
    · refine key (b.1.insert a, b.2.enqueue a) (h.enqueue a) (fun x hx => ?_) ?_ ?_
      · show (b.1.insert a).contains x = true
        rw [Std.HashSet.contains_insert, hx, Bool.or_true]
      · show (b.1.insert a).contains a = true
        simp [Std.HashSet.contains_insert]
      · simp [List.forIn_cons, StateT.run, seedStep, hc, bind, StateT.bind, pure, StateT.pure]

/-- **A worklist run that reports itself drained has done every seed**, when processing an
    item makes it done, keeps done items done, and done is closed under `==`. -/
theorem run_complete [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (Done : σ → α → Prop) (process : α → StateM σ (List α))
    (hmono : ∀ a s x, Done s x → Done ((process a).run s).2 x)
    (hdone : ∀ a s, Done ((process a).run s).2 a)
    (hbeq : ∀ s x y, (x == y) = true → Done s y → Done s x)
    (initial : List α) (cap : Nat) (s : σ)
    (hfin : ((Strata.Worklist.run initial process cap).run s).1 = true) :
    ∀ a ∈ initial, Done ((Strata.Worklist.run initial process cap).run s).2 a := by
  unfold Strata.Worklist.run at hfin ⊢
  simp only [StateT.run, bind, StateT.bind] at hfin ⊢
  have hseed := forIn_seed Done s initial (∅, ∅) s
    (fun x hx => by simp at hx)
  simp only [StateT.run] at hseed
  change (match forIn initial (∅, ∅) seedStep s with
      | (a, s) => Strata.Worklist.runIterations process cap (a.snd, a.fst) s).fst = true at hfin
  change ∀ a ∈ initial, Done (match forIn initial (∅, ∅) seedStep s with
      | (a, s) => Strata.Worklist.runIterations process cap (a.snd, a.fst) s).snd a
  obtain ⟨hinv, -, hall, hst⟩ := hseed
  generalize forIn initial (∅, ∅) seedStep s = r at hinv hall hst hfin ⊢
  obtain ⟨⟨S, Q⟩, s'⟩ := r
  simp only at hinv hall hst hfin ⊢
  subst hst
  intro a ha
  exact runIterations_complete Done process hmono hdone hbeq cap (Q, S) s' hinv hfin a (hall a ha)


/-! #### Closure: a drained run has done every successor of a marked item -/

/-- The enqueue step of `runOneIter`. -/
private abbrev enqStep [BEq α] [Hashable α] (x : Std.Queue α × Std.HashSet α) (b : α) :
    StateM σ (Std.Queue α × Std.HashSet α) :=
  if x.snd.contains b = true then pure (x.fst, x.snd)
  else pure (Std.Queue.enqueue b x.fst, x.snd.insert b)

/-- The enqueue fold sees every item it folds over and keeps what was seen. -/
private theorem foldlM_enqStep_seen [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] :
    ∀ (l : List α) (x : Std.Queue α × Std.HashSet α) (s : σ),
      (∀ y, x.2.contains y = true → ((l.foldlM enqStep x).run s).1.2.contains y = true) ∧
      ∀ b ∈ l, ((l.foldlM enqStep x).run s).1.2.contains b = true
  | [], x, s => ⟨fun _ h => h, fun _ hb => absurd hb List.not_mem_nil⟩
  | b :: l, x, s => by
    have key : ∀ x' : Std.Queue α × Std.HashSet α, (∀ y, x.2.contains y = true → x'.2.contains y =
        true) →
        x'.2.contains b = true → ((b :: l).foldlM enqStep x).run s = (l.foldlM enqStep x').run s →
        (∀ y, x.2.contains y = true → (((b :: l).foldlM enqStep x).run s).1.2.contains y = true) ∧
        ∀ b' ∈ b :: l, (((b :: l).foldlM enqStep x).run s).1.2.contains b' = true := by
      intro x' hsub hb heq
      rw [heq]
      obtain ⟨h1, h2⟩ := foldlM_enqStep_seen l x' s
      refine ⟨fun y hy => h1 y (hsub y hy), fun b' hb' => ?_⟩
      rcases List.mem_cons.mp hb' with rfl | hb'
      · exact h1 _ hb
      · exact h2 b' hb'
    by_cases hc : x.2.contains b = true
    · exact key x (fun _ h => h) hc (by simp [List.foldlM_cons, enqStep, hc, StateT.run, bind,
        StateT.bind, pure, StateT.pure])
    · refine key (x.1.enqueue b, x.2.insert b) (fun y hy => ?_) ?_ ?_
      · show (x.2.insert b).contains y = true
        rw [Std.HashSet.contains_insert, hy, Bool.or_true]
      · show (x.2.insert b).contains b = true
        simp [Std.HashSet.contains_insert]
      · simp [List.foldlM_cons, enqStep, hc, StateT.run, bind, StateT.bind, pure, StateT.pure]

/-- Every successor of a marked item has been seen. -/
def MarkInv [BEq α] [Hashable α] (Mark : σ → α → Prop) (next : α → List α)
    (S : Std.HashSet α) (s : σ) : Prop :=
  ∀ a, Mark s a → ∀ b ∈ next a, S.contains b = true

/-- One iteration keeps `MarkInv`, when processing `a` returns its successors and marks
    nothing but `a`. -/
private theorem runOneIter_mark [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (Mark : σ → α → Prop) (next : α → List α) (process : α → StateM σ (List α))
    (hnext : ∀ a s, ∀ b ∈ next a, b ∈ ((process a).run s).1)
    (hmark : ∀ a s x, Mark ((process a).run s).2 x → Mark s x ∨ x = a)
    (st : Std.Queue α × Std.HashSet α) (s : σ) (h : MarkInv Mark next st.2 s) :
    ∀ st', ((Strata.Worklist.runOneIter process st).run s).1 = some st' →
      MarkInv Mark next st'.2 ((Strata.Worklist.runOneIter process st).run s).2 := by
  unfold Strata.Worklist.runOneIter
  simp only [StateT.run, bind]
  rcases hdq : st.fst.dequeue? with _ | ⟨a, pending⟩
  · intro st' hst'
    simp [pure, StateT.pure] at hst'
  · intro st' hst'
    simp only [StateT.bind] at hst' ⊢
    have hn := hnext a s
    have hm := hmark a s
    simp only [StateT.run] at hn hm
    generalize process a s = r at hn hm hst' ⊢
    obtain ⟨news, s1⟩ := r
    simp only at hn hm hst' ⊢
    have hseen := foldlM_enqStep_seen (σ := σ) news (pending, st.snd) s1
    have hst := foldlM_state_inv (· = s1) news enqStep
      (fun b _ x s hs => by simp only [enqStep]; split <;> exact hs) (pending, st.snd) s1 rfl
    simp only [StateT.run] at hseen hst
    change ((List.foldlM enqStep (pending, st.snd) news : StateM σ _) s1 |>.fst |> some) = some st'
      at hst'
    change MarkInv Mark next st'.2 ((List.foldlM enqStep (pending, st.snd) news : StateM σ _) s1).2
    rw [hst]
    simp only [Option.some.injEq] at hst'
    subst hst'
    intro x hx b hb
    rcases hm x hx with hx | rfl
    · exact hseen.1 b (h x hx b hb)
    · exact hseen.2 b (hn b hb)

/-- Iterating keeps `CompleteInv` and `MarkInv`; when the run reports itself drained, every
    successor of a marked item is done. -/
private theorem runIterations_closed [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (Done Mark : σ → α → Prop) (next : α → List α) (process : α → StateM σ (List α))
    (hmono : ∀ a s x, Done s x → Done ((process a).run s).2 x)
    (hdone : ∀ a s, Done ((process a).run s).2 a)
    (hbeq : ∀ s x y, (x == y) = true → Done s y → Done s x)
    (hnext : ∀ a s, ∀ b ∈ next a, b ∈ ((process a).run s).1)
    (hmark : ∀ a s x, Mark ((process a).run s).2 x → Mark s x ∨ x = a) :
    ∀ n (st : Std.Queue α × Std.HashSet α) s, CompleteInv Done st.1 st.2 s →
      MarkInv Mark next st.2 s →
      ((Strata.Worklist.runIterations process n st).run s).1 = true →
      ∀ a, Mark ((Strata.Worklist.runIterations process n st).run s).2 a →
        ∀ b ∈ next a, Done ((Strata.Worklist.runIterations process n st).run s).2 b
  | 0, st, s, hc, hm, hfin, a, ha, b, hb => by
    obtain ⟨pending, seen⟩ := st
    unfold Strata.Worklist.runIterations at hfin ha ⊢
    exact runIterations_complete Done process hmono hdone hbeq 0 (pending, seen) s hc
      (by unfold Strata.Worklist.runIterations; exact hfin) b (hm a ha b hb)
  | n + 1, st, s, hc, hm, hfin, a, ha, b, hb => by
    unfold Strata.Worklist.runIterations at hfin ha ⊢
    simp only [StateT.run, bind, StateT.bind] at hfin ha ⊢
    have h2 := runOneIter_complete Done process hmono hdone hbeq st s hc
    have h3 := runOneIter_mark Mark next process hnext hmark st s hm
    simp only [StateT.run] at h2 h3
    generalize Strata.Worklist.runOneIter process st s = r at h2 h3 hfin ha ⊢
    obtain ⟨o, s2⟩ := r
    rcases h2 with ⟨ho, hs2, hq⟩ | ⟨st', ho, hd⟩
    · simp only at ho hs2
      subst ho hs2
      rcases hc b (hm a ha b hb) with h | ⟨y, hy, -⟩
      · exact h
      · rw [hq] at hy; cases hy
    · simp only at ho hd
      subst ho
      exact runIterations_closed Done Mark next process hmono hdone hbeq hnext hmark n st' s2
        hd.1 (h3 st' rfl) hfin a ha b hb

/-- **A drained worklist run has done every successor of every item it marked**, when
    processing an item returns its successors, makes it done and marks only it, done items stay
    done, done is closed under `==`, and nothing is marked at the start. -/
theorem run_closed [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (Done Mark : σ → α → Prop) (next : α → List α) (process : α → StateM σ (List α))
    (hmono : ∀ a s x, Done s x → Done ((process a).run s).2 x)
    (hdone : ∀ a s, Done ((process a).run s).2 a)
    (hbeq : ∀ s x y, (x == y) = true → Done s y → Done s x)
    (hnext : ∀ a s, ∀ b ∈ next a, b ∈ ((process a).run s).1)
    (hmark : ∀ a s x, Mark ((process a).run s).2 x → Mark s x ∨ x = a)
    (initial : List α) (cap : Nat) (s : σ) (h0 : ∀ a, ¬ Mark s a)
    (hfin : ((Strata.Worklist.run initial process cap).run s).1 = true) :
    ∀ a, Mark ((Strata.Worklist.run initial process cap).run s).2 a →
      ∀ b ∈ next a, Done ((Strata.Worklist.run initial process cap).run s).2 b := by
  unfold Strata.Worklist.run at hfin ⊢
  simp only [StateT.run, bind, StateT.bind] at hfin ⊢
  have hseed := forIn_seed Done s initial (∅, ∅) s (fun x hx => by simp at hx)
  simp only [StateT.run] at hseed
  change (match forIn initial (∅, ∅) seedStep s with
      | (a, s) => Strata.Worklist.runIterations process cap (a.snd, a.fst) s).fst = true at hfin
  change ∀ a, Mark (match forIn initial (∅, ∅) seedStep s with
      | (a, s) => Strata.Worklist.runIterations process cap (a.snd, a.fst) s).snd a →
    ∀ b ∈ next a, Done (match forIn initial (∅, ∅) seedStep s with
      | (a, s) => Strata.Worklist.runIterations process cap (a.snd, a.fst) s).snd b
  obtain ⟨hinv, -, -, hst⟩ := hseed
  generalize forIn initial (∅, ∅) seedStep s = r at hinv hst hfin ⊢
  obtain ⟨⟨S, Q⟩, s'⟩ := r
  simp only at hinv hst hfin ⊢
  subst hst
  exact runIterations_closed Done Mark next process hmono hdone hbeq hnext hmark cap (Q, S) s'
    hinv (fun a ha => absurd ha (h0 a)) hfin

end -- public section

end Strata.Worklist
