/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Experiment.HM.Subst
import Strata.DL.Util.List

/-! ## Robinson Unification for Hindley-Milner -/

namespace HM

/-- Occurs check: does type variable `n` appear in `τ`? -/
def Ty.occurs (n : Nat) : Ty → Bool
  | .var m => n == m
  | .con _ args => args.attach.any fun ⟨t, _⟩ => t.occurs n
termination_by t => t
decreasing_by term_by_mem

---------------------------------------------------------------------
-- Variable sets
---------------------------------------------------------------------

/-- Collect all type variable indices across a list of types. -/
def Ty.varsOfList (ts : List Ty) : List Nat :=
  ts.flatMap Ty.freeVars

---------------------------------------------------------------------
-- Constraint representation
---------------------------------------------------------------------

/-- A unification constraint: two types that must be equal. -/
abbrev Constraint := Ty × Ty

/-- A list of unification constraints. -/
abbrev Constraints := List Constraint

/-- Free variables in a constraint. -/
def Constraint.vars (c : Constraint) : List Nat :=
  c.1.freeVars ++ c.2.freeVars

/-- Free variables across a list of constraints. -/
def Constraints.vars : Constraints → List Nat
  | [] => []
  | c :: cs => c.vars ++ Constraints.vars cs

/-- Size of a constraint (sum of type sizes). -/
def Constraint.size (c : Constraint) : Nat :=
  c.1.size + c.2.size

/-- Total size of a list of constraints. -/
def Constraints.size : Constraints → Nat
  | [] => 0
  | c :: cs => c.size + Constraints.size cs

---------------------------------------------------------------------
-- Termination measure
---------------------------------------------------------------------

/-- The termination measure: distinct vars in constraints + substitution range. -/
noncomputable def unifyMeasure (cs : Constraints) (S : Subst) : Nat :=
  (Constraints.vars cs ++ substFreeVars S).dedup.length

---------------------------------------------------------------------
-- Termination lemmas
---------------------------------------------------------------------

-- vars of a con's args = vars of the con
theorem Ty.vars_con (n : String) (as : List Ty) :
    Ty.freeVars (.con n as) = Ty.varsOfList as := by
  simp [Ty.freeVars, Ty.varsOfList]

-- varsOfList is monotone under cons
theorem Ty.varsOfList_subset_cons (a : Ty) (as : List Ty) :
    ∀ v, v ∈ Ty.varsOfList as → v ∈ Ty.varsOfList (a :: as) := by
  intro v hv; simp [Ty.varsOfList] at *; grind

-- Applying a substitution: new vars come from the range.
theorem Ty.vars_apply_subset (S : Subst) :
    ∀ t : Ty, ∀ v, v ∈ (S.apply t).freeVars →
      v ∈ t.freeVars ∨ ∃ n τ, S.find? n = some τ ∧ v ∈ τ.freeVars ∧ n ∈ t.freeVars := by
  intro t
  induction t using Ty.ind' with
  | hvar n =>
    intro v hv
    simp [Subst.apply] at hv
    split at hv
    · rename_i τ hfind
      right; exact ⟨n, τ, hfind, hv, by simp [Ty.freeVars]⟩
    · left; exact hv
  | hcon name args ih =>
    intro v hv
    have : v ∈ Ty.varsOfList (args.map S.apply) := by
      simp [Ty.varsOfList, Subst.apply, Ty.freeVars] at hv ⊢; exact hv
    simp [Ty.varsOfList] at this
    obtain ⟨t, ⟨t₀, ht₀_mem, rfl⟩, hv_t⟩ := this
    have := ih t₀ ht₀_mem v hv_t
    cases this with
    | inl h =>
      left; simp [Ty.freeVars]; exact ⟨t₀, ht₀_mem, h⟩
    | inr h =>
      obtain ⟨n, τ, hfind, hv_τ, hn_t⟩ := h
      right; refine ⟨n, τ, hfind, hv_τ, ?_⟩
      simp [Ty.freeVars]; exact ⟨t₀, ht₀_mem, hn_t⟩

-- Lifting to lists
theorem Ty.varsOfList_map_apply_subset (S : Subst) (ts : List Ty) :
    ∀ v, v ∈ Ty.varsOfList (ts.map S.apply) →
      v ∈ Ty.varsOfList ts ∨ ∃ n τ, S.find? n = some τ ∧ v ∈ τ.freeVars ∧ n ∈ Ty.varsOfList ts := by
  intro v hv
  simp [Ty.varsOfList] at *
  obtain ⟨t, ⟨t₀, ht₀_mem, rfl⟩, hv_t⟩ := hv
  have := Ty.vars_apply_subset S t₀ v hv_t
  cases this with
  | inl h => left; exact ⟨t₀, ht₀_mem, h⟩
  | inr h =>
    obtain ⟨n, τ, hfind, hv_τ, hn_t₀⟩ := h
    right; exact ⟨n, τ, hfind, hv_τ, t₀, ht₀_mem, hn_t₀⟩

-- dedup.length is monotone under subset
theorem List.dedup_length_le_of_subset [DecidableEq α]
    {l₁ l₂ : List α} (h : ∀ x, x ∈ l₁ → x ∈ l₂) :
    l₁.dedup.length ≤ l₂.dedup.length :=
  List.length_dedup_of_subset_le l₁ l₂ h

---------------------------------------------------------------------
-- Unification (S-accumulator style, following LTyUnify)
---------------------------------------------------------------------

/-- The new substitution's free vars are bounded by the constraint vars + old subst vars. -/
def substBounded (cs : Constraints) (newS oldS : Subst) : Prop :=
  substFreeVars newS ⊆ Constraints.vars cs ++ substFreeVars oldS

/-- A substitution bundled with a proof that its free vars are bounded. -/
structure ValidSubst (cs : Constraints) (oldS : Subst) where
  subst : Subst
  bounded : substBounded cs subst oldS

---------------------------------------------------------------------
-- Decreasing lemmas
---------------------------------------------------------------------

-- substFreeVars of a cons
@[simp] theorem substFreeVars_cons (n : Nat) (ty : Ty) (S : Subst) :
    substFreeVars ((n, ty) :: S) = ty.freeVars ++ substFreeVars S := by
  simp [substFreeVars, Map.values]

-- substBounded is reflexive (S unchanged)
theorem substBounded_refl (cs : Constraints) (S : Subst) :
    substBounded cs S S := by
  simp [substBounded]

-- Adding a binding whose vars come from the constraint
theorem substBounded_cons (c : Constraint) (S : Subst) (n : Nat) (ty : Ty)
    (hty : ty.freeVars ⊆ Constraint.vars c ++ substFreeVars S) :
    substBounded [c] ((n, ty) :: S) S := by
  simp [substBounded, substFreeVars_cons, Constraints.vars]
  intro v hv
  grind

-- Vars of S.apply t are in t.freeVars ++ substFreeVars S
theorem vars_apply_subset_freeVars (S : Subst) (t : Ty) :
    (S.apply t).freeVars ⊆ t.freeVars ++ substFreeVars S := by
  intro v hv
  have := Ty.vars_apply_subset S t v hv
  cases this with
  | inl h => exact List.mem_append_left _ h
  | inr h =>
    obtain ⟨n, τ, hfind, hv_τ, _⟩ := h
    apply List.mem_append_right
    simp [substFreeVars]
    have h:= List.mem_flatMap.mpr ⟨τ, Map.find?_mem_values S hfind, hv_τ⟩
    simp at h; exact h

-- Adding (n, S.apply t) to S is bounded by [(s,t)]
theorem substBounded_cons_apply_snd (s t : Ty) (S : Subst) (n : Nat) :
    substBounded [(s, t)] ((n, S.apply t) :: S) S := by
  apply substBounded_cons
  intro v hv
  have := vars_apply_subset_freeVars S t hv
  simp [Constraint.vars, List.mem_append] at this ⊢
  grind

theorem substBounded_cons_apply_fst (s t : Ty) (S : Subst) (n : Nat) :
    substBounded [(s, t)] ((n, S.apply s) :: S) S := by
  apply substBounded_cons
  intro v hv
  have := vars_apply_subset_freeVars S s hv
  simp [Constraint.vars, List.mem_append] at this ⊢
  grind

-- Goal 1: unifyOne(c=(s,t), S) → unifyCore(as.zip bs, S)
-- where S.apply s = con n as, S.apply t = con m bs
-- Need: unifyMeasure (as.zip bs) S < unifyMeasure [(s,t)] S
--     ∨ unifyMeasure equal ∧ Constraints.size (as.zip bs) < Constraint.size (s,t)
-- Vars of a zip are a subset of the vars of both lists
theorem Constraints.vars_zip_subset (as bs : List Ty) :
    Constraints.vars (as.zip bs) ⊆ Ty.varsOfList as ++ Ty.varsOfList bs := by
  induction as generalizing bs with
  | nil => simp [Constraints.vars]
  | cons a as ih =>
    cases bs with
    | nil => simp [Constraints.vars]
    | cons b bs =>
      simp only [List.zip_cons_cons, Constraints.vars, Constraint.vars, Ty.varsOfList,
        List.flatMap_cons]
      intro v hv
      simp only [List.mem_append] at hv ⊢
      rcases hv with (h | h) | h
      · left; left; exact h
      · right; left; exact h
      · have := ih bs h; simp [Ty.varsOfList, List.mem_append] at this
        grind

theorem Constraints.vars_zip_superset (h : as.length = bs.length) :
    Ty.varsOfList as ++ Ty.varsOfList bs ⊆ Constraints.vars (as.zip bs) := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all [Ty.varsOfList]
  | cons a as ih =>
    cases bs with
    | nil => simp at h
    | cons b bs =>
      intro v hv
      simp at h
      simp only [List.zip_cons_cons, Constraints.vars, Constraint.vars, Ty.varsOfList,
        List.flatMap_cons, List.mem_append] at hv ⊢
      rcases hv with (h₁ | h₁) | (h₁ | h₁)
      · left; left; exact h₁
      · right; exact ih h (by simp [Ty.varsOfList, List.mem_append]; left; grind)
      · left; right; exact h₁
      · right; exact ih h (by simp [Ty.varsOfList, List.mem_append]; right; grind)

theorem Constraints.size_zip_eq (h : as.length = bs.length) :
    Constraints.size (as.zip bs) = Ty.sizeList as + Ty.sizeList bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all [Constraints.size, Ty.sizeList]
  | cons a as ih =>
    cases bs with
    | nil => simp at h
    | cons b bs =>
      simp at h
      simp [List.zip, Constraints.size, Constraint.size, Ty.sizeList]
      have := ih h; simp [List.zip] at this; omega

/-
Proof (zip_le):
  Right disjunct: measure = and size <.

  1. Measure =: Constraints.vars(as.zip bs) has same dedup length as
     freeVars(con n as) ++ freeVars(con m bs), since zip vars = varsOfList as ++ varsOfList bs
     = freeVars(con n as) ++ freeVars(con m bs) (when lengths equal).

  2. Size <: Constraints.size(as.zip bs) = sizeList as + sizeList bs
     < (1 + sizeList as) + (1 + sizeList bs) = Constraint.size(con n as, con m bs).
-/
theorem unifyMeasure_zip_le (as bs : List Ty) (n m : String) (S : Subst)
    (h : as.length = bs.length) :
    unifyMeasure (as.zip bs) S < unifyMeasure [(.con n as, .con m bs)] S ∨
    unifyMeasure (as.zip bs) S = unifyMeasure [(.con n as, .con m bs)] S ∧
      Constraints.size (as.zip bs) < Constraint.size (.con n as, .con m bs) := by
  -- Both directions of the var subset (zip vars = con vars)
  have h_sub : Constraints.vars (as.zip bs) ⊆
      Constraints.vars [(.con n as, .con m bs)] := by
    intro v hv
    have := Constraints.vars_zip_subset as bs hv
    simp only [Constraints.vars, Constraint.vars, Ty.vars_con, List.mem_append] at this ⊢
    grind
  have h_sup : Constraints.vars [(.con n as, .con m bs)] ⊆
      Constraints.vars (as.zip bs) := by
    intro v hv
    simp only [Constraints.vars, Constraint.vars, Ty.freeVars,
      List.mem_append] at hv
    exact Constraints.vars_zip_superset h (by simp [Ty.varsOfList, List.mem_append]; grind)
  right; constructor
  · -- measure =
    apply Nat.le_antisymm <;> apply List.dedup_length_le_of_subset <;>
      intro v hv <;> simp [List.mem_append] at hv ⊢
    · rcases hv with h₁ | h₁
      · left; exact h_sub h₁
      · right; exact h₁
    · rcases hv with h₁ | h₁
      · left; exact h_sup h₁
      · right; exact h₁
  · -- size <
    simp [Constraints.size_zip_eq h, Constraint.size, Ty.size]; omega

-- Goal 2: unifyCore(c::cs, S) → unifyOne(c, S)
-- Need: unifyMeasure [c] S < unifyMeasure (c::cs) S
--     ∨ unifyMeasure equal ∧ (c.size < Constraints.size (c::cs) ∨ c.size = ...)
theorem unifyMeasure_single_le (c : Constraint) (cs : Constraints) (S : Subst) :
    unifyMeasure [c] S < unifyMeasure (c :: cs) S ∨
    unifyMeasure [c] S = unifyMeasure (c :: cs) S ∧
      (c.size < Constraints.size (c :: cs) ∨ c.size = Constraints.size (c :: cs)) := by
  have hle : unifyMeasure [c] S ≤ unifyMeasure (c :: cs) S := by
    apply List.dedup_length_le_of_subset
    intro v hv; simp [List.mem_append, Constraints.vars] at hv ⊢; grind
  cases Nat.lt_or_eq_of_le hle with
  | inl h => left; exact h
  | inr h =>
    right; constructor
    · exact h
    · simp [Constraints.size, Constraint.size]; omega

-- Goal 3: unifyCore(c::cs, S) → unifyCore(cs, S₁) where S₁.bounded : substBounded [c] S₁ S
-- Need: (unifyMeasure cs S₁, Constraints.size cs, 1) <ₗₑₓ (unifyMeasure (c::cs) S, Constraints.size (c::cs), 1)
/-
Proof:
  1. substFreeVars S₁ ⊆ c.vars ++ substFreeVars S  (from hb)
  2. Constraints.vars cs ++ substFreeVars S₁ ⊆ c.vars ++ Constraints.vars cs ++ substFreeVars S
  3. unifyMeasure cs S₁ ≤ unifyMeasure (c::cs) S  (by dedup monotonicity)
  4. Constraints.size cs < Constraints.size (c::cs)  (since c.size > 0)
  5. Lex order: first ≤ with second <, so lex holds.
-/
theorem unifyMeasure_tail_lt (c : Constraint) (cs : Constraints) (S S₁ : Subst)
    (hb : substBounded [c] S₁ S) :
    Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))
      (unifyMeasure cs S₁, Constraints.size cs, 1)
      (unifyMeasure (c :: cs) S, Constraints.size (c :: cs), 1) := by
  -- Step 1: substFreeVars S₁ ⊆ c.vars ++ substFreeVars S
  simp [substBounded, Constraints.vars] at hb
  -- Step 2: subset of the full variable pool
  have hsub : ∀ v, v ∈ Constraints.vars cs ++ substFreeVars S₁ →
      v ∈ Constraints.vars (c :: cs) ++ substFreeVars S := by
    intro v hv
    simp [List.mem_append, Constraints.vars] at hv ⊢
    grind
  -- Step 3: unifyMeasure cs S₁ ≤ unifyMeasure (c::cs) S
  have hle : unifyMeasure cs S₁ ≤ unifyMeasure (c :: cs) S :=
    List.dedup_length_le_of_subset hsub
  -- Step 4: Constraints.size cs < Constraints.size (c::cs)
  have hlt : Constraints.size cs < Constraints.size (c :: cs) := by
    simp [Constraints.size]
    have := Ty.size_pos c.1; have := Ty.size_pos c.2
    simp [Constraint.size]; omega
  -- Step 5: lex order
  grind

-- Lifting substBounded from zip to the original constraint
theorem substBounded_zip_to_con (n m : String) (as bs : List Ty) (S newS : Subst)
    (hb : substBounded (as.zip bs) newS S) :
    substBounded [(.con n as, .con m bs)] newS S := by
  intro v hv
  have := hb hv
  simp [List.mem_append] at this ⊢
  rcases this with h | h
  · left; simp [Constraints.vars, Constraint.vars, Ty.vars_con, List.mem_append]
    exact List.mem_append.mp (Constraints.vars_zip_subset as bs h)
  · right; exact h

-- Composing two substBounded proofs
theorem substBounded_trans (c : Constraint) (cs : Constraints) (S S₁ S₂ : Subst)
    (h₁ : substBounded [c] S₁ S) (h₂ : substBounded cs S₂ S₁) :
    substBounded (c :: cs) S₂ S := by
  intro v hv
  have := h₂ hv
  simp [List.mem_append, Constraints.vars] at this ⊢
  rcases this with h | h
  · grind
  · have := h₁ h; simp [List.mem_append, Constraints.vars] at this; grind

mutual
/-- Unify a single constraint, accumulating into S.
    Match on original types (not S-applied) so con/con decomposition decreases size. -/
def unifyOne (c : Constraint) (S : Subst) : Except String (ValidSubst [c] S) :=
  match c with
  | (.var n, t) =>
    let t' := S.apply t
    let s' := S.apply (.var n)
    if s' == t' then .ok ⟨S, substBounded_refl _ S⟩
    else if t'.occurs n then .error s!"occurs check: {n} in {repr t'}"
    else .ok ⟨(n, t') :: S, substBounded_cons_apply_snd (.var n) t S n⟩
  | (s, .var n) =>
    let s' := S.apply s
    let t' := S.apply (.var n)
    if t' == s' then .ok ⟨S, substBounded_refl _ S⟩
    else if s'.occurs n then .error s!"occurs check: {n} in {repr s'}"
    else .ok ⟨(n, s') :: S, substBounded_cons_apply_fst s (.var n) S n⟩
  | (.con n as, .con m bs) =>
    if _h : n = m ∧ as.length = bs.length then
      match unifyCore (as.zip bs) S with
      | .ok r => .ok ⟨r.subst, substBounded_zip_to_con n m as bs S r.subst r.bounded⟩
      | .error e => .error e
    else .error s!"constructor mismatch: {n} ≠ {m}"
termination_by (unifyMeasure [c] S, Constraint.size c, 0)
decreasing_by
  simp_all [Prod.lex_def]
  exact unifyMeasure_zip_le as bs m m S _h.2

/-- Unify a list of constraints, accumulating into S. -/
def unifyCore (cs : Constraints) (S : Subst) : Except String (ValidSubst cs S) :=
  match cs with
  | [] => .ok ⟨S, by simp [substBounded]⟩
  | c :: cs => do
    let r₁ ← unifyOne c S
    let r₂ ← unifyCore cs r₁.subst
    .ok ⟨r₂.subst, substBounded_trans c cs S r₁.subst r₂.subst r₁.bounded r₂.bounded⟩
termination_by (unifyMeasure cs S, Constraints.size cs, 1)
decreasing_by
  · -- unifyCore(c::cs, S) → unifyOne(c, S)
    simp_all [Prod.lex_def]
    exact unifyMeasure_single_le c cs S
  · -- unifyCore(c::cs, S) → unifyCore(cs, r₁.subst)
    have hb := r₁.bounded
    exact unifyMeasure_tail_lt c cs S r₁.subst hb
end

/-- Top-level unification of two types. -/
def unify (s t : Ty) : Except String Subst :=
  (unifyOne (s, t) Subst.id).map (·.subst)

/-- Top-level unification of two type lists. -/
def unifyList (as bs : List Ty) : Except String Subst :=
  (unifyCore (as.zip bs) Subst.id).map (·.subst)

end HM
