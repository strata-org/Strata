/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.LaurelSemantics

/-!
# Properties of Laurel Operational Semantics

Determinism, store monotonicity, and progress properties for the
direct Laurel operational semantics.
-/

namespace Strata.Laurel

/-! ## Store Monotonicity -/

theorem UpdateStore_def_monotone {σ σ' : LaurelStore} {x : Identifier} {v : LaurelValue}
    {vs : List Identifier} :
    (∀ y, y ∈ vs → (σ y).isSome) →
    UpdateStore σ x v σ' →
    (∀ y, y ∈ vs → (σ' y).isSome) := by
  intro Hdef Hup y Hy
  cases Hup with
  | update Hold Hnew Hrest =>
    by_cases heq : x = y
    · subst heq; simp [Hnew]
    · rw [Hrest y heq]; exact Hdef y Hy

theorem InitStore_def_monotone {σ σ' : LaurelStore} {x : Identifier} {v : LaurelValue}
    {vs : List Identifier} :
    (∀ y, y ∈ vs → (σ y).isSome) →
    InitStore σ x v σ' →
    (∀ y, y ∈ vs → (σ' y).isSome) := by
  intro Hdef Hinit y Hy
  cases Hinit with
  | init Hnone Hnew Hrest =>
    by_cases heq : x = y
    · subst heq; simp [Hnew]
    · rw [Hrest y heq]; exact Hdef y Hy

/-! ## Determinism of Store Operations -/

theorem UpdateStore_deterministic {σ σ₁ σ₂ : LaurelStore} {x : Identifier} {v : LaurelValue} :
    UpdateStore σ x v σ₁ →
    UpdateStore σ x v σ₂ →
    σ₁ = σ₂ := by
  intro H1 H2
  cases H1 with | update _ Hnew1 Hrest1 =>
  cases H2 with | update _ Hnew2 Hrest2 =>
  funext y
  by_cases heq : x = y
  · subst heq; simp_all
  · rw [Hrest1 y heq, Hrest2 y heq]

theorem InitStore_deterministic {σ σ₁ σ₂ : LaurelStore} {x : Identifier} {v : LaurelValue} :
    InitStore σ x v σ₁ →
    InitStore σ x v σ₂ →
    σ₁ = σ₂ := by
  intro H1 H2
  cases H1 with | init _ Hnew1 Hrest1 =>
  cases H2 with | init _ Hnew2 Hrest2 =>
  funext y
  by_cases heq : x = y
  · subst heq; simp_all
  · rw [Hrest1 y heq, Hrest2 y heq]

/-! ## Determinism of Heap Operations -/

/-- AllocHeap is deterministic because the `alloc` constructor requires `addr`
to be the smallest free address (all smaller addresses are occupied). -/
theorem AllocHeap_deterministic {h h₁ h₂ : LaurelHeap}
    {typeName : Identifier} {addr₁ addr₂ : Nat} :
    AllocHeap h typeName addr₁ h₁ →
    AllocHeap h typeName addr₂ h₂ →
    addr₁ = addr₂ ∧ h₁ = h₂ := by
  intro H1 H2
  match H1, H2 with
  | .alloc hfree1 hmin1 hnew1 hrest1, .alloc hfree2 hmin2 hnew2 hrest2 =>
    have haddr : addr₁ = addr₂ := by
      if heq : addr₁ = addr₂ then exact heq
      else
        cases Nat.lt_or_gt_of_ne heq with
        | inl hlt => exact absurd (hmin2 addr₁ hlt) (by simp [hfree1])
        | inr hgt => exact absurd (hmin1 addr₂ hgt) (by simp [hfree2])
    subst haddr
    exact ⟨rfl, funext fun a => by
      if heq : addr₁ = a then subst heq; rw [hnew1, hnew2]
      else rw [hrest1 a heq, hrest2 a heq]⟩

theorem HeapFieldWrite_deterministic {h h₁ h₂ : LaurelHeap}
    {addr : Nat} {field : Identifier} {v : LaurelValue} :
    HeapFieldWrite h addr field v h₁ →
    HeapFieldWrite h addr field v h₂ →
    h₁ = h₂ := by
  intro H1 H2
  cases H1 with | write Hlook1 Hnew1 Hrest1 =>
  cases H2 with | write Hlook2 Hnew2 Hrest2 =>
  funext a
  by_cases heq : addr = a
  · subst heq
    rw [Hlook1] at Hlook2
    have := Option.some.inj Hlook2
    simp_all
  · rw [Hrest1 a heq, Hrest2 a heq]

/-! ## Determinism of EvalArgs -/

/-- Determinism of the non-mutual `EvalArgs` (pure expression evaluation).
This is retained for reasoning about pure sub-expressions where `EvalStmtArgs`
is not needed. The mutual `EvalStmtArgs_deterministic` (in the determinism
mutual block below) handles the effectful case. -/
theorem EvalArgs_deterministic {δ : LaurelEval} {σ : LaurelStore}
    {es : List StmtExprMd} {vs₁ vs₂ : List LaurelValue} :
    EvalArgs δ σ es vs₁ →
    EvalArgs δ σ es vs₂ →
    vs₁ = vs₂ := by
  intro H1 H2
  induction H1 generalizing vs₂ with
  | nil => cases H2; rfl
  | cons hev₁ _ ih =>
    cases H2 with
    | cons hev₂ htail₂ =>
      rw [hev₁] at hev₂
      have := Option.some.inj hev₂
      subst this
      congr 1
      exact ih htail₂

/-! ## catchExit Properties -/

theorem catchExit_normal (label : Option Identifier) (v : LaurelValue) :
    catchExit label (.normal v) = .normal v := by
  cases label <;> simp [catchExit]

theorem catchExit_return (label : Option Identifier) (rv : Option LaurelValue) :
    catchExit label (.ret rv) = .ret rv := by
  cases label <;> simp [catchExit]

theorem catchExit_none_passthrough (o : Outcome) :
    catchExit none o = o := by
  simp [catchExit]

/-! ## Determinism of Evaluation

AllocHeap was made deterministic (smallest-free-address policy) so that
full determinism `h₁ = h₂ ∧ σ₁ = σ₂ ∧ o₁ = o₂` holds for all constructors
including `new_obj`.

The proof uses mutual structural recursion on the first derivation (term-mode
`match` on H1, then tactic-mode `cases` on H2 inside each branch).
-/

-- TODO: maxHeartbeats 800000 is ~4× the default. Consider extracting a helper
-- lemma for the shared call-case prefix (proc lookup, EvalStmtArgs, bind,
-- getBody, then outcome discrimination) to reduce ~150 lines of repetition
-- and lower heartbeat pressure. With EvalStmtArgs, the prefix now includes
-- heap/store threading from argument evaluation.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
mutual
theorem EvalLaurelStmt_deterministic
    {δ : LaurelEval} {π : ProcEnv} {h : LaurelHeap} {σ : LaurelStore}
    {s : StmtExprMd} {h₁ h₂ : LaurelHeap} {σ₁ σ₂ : LaurelStore} {o₁ o₂ : Outcome}
    (H1 : EvalLaurelStmt δ π h σ s h₁ σ₁ o₁)
    (H2 : EvalLaurelStmt δ π h σ s h₂ σ₂ o₂) :
    h₁ = h₂ ∧ σ₁ = σ₂ ∧ o₁ = o₂ :=
  match H1 with
  -- Literals and leaf nodes (no sub-derivations)
  | .literal_int => by cases H2; exact ⟨rfl, rfl, rfl⟩
  | .literal_bool => by cases H2; exact ⟨rfl, rfl, rfl⟩
  | .literal_string => by cases H2; exact ⟨rfl, rfl, rfl⟩
  | .identifier _ => by cases H2; simp_all
  | .exit_sem => by cases H2; exact ⟨rfl, rfl, rfl⟩
  | .return_none => by cases H2; exact ⟨rfl, rfl, rfl⟩
  | .this_sem _ => by cases H2; simp_all
  -- Specification constructs delegated to δ
  | .forall_sem h1 => by cases H2 with | forall_sem h2 => rw [h1] at h2; simp_all
  | .exists_sem h1 => by cases H2 with | exists_sem h2 => rw [h1] at h2; simp_all
  | .old_sem h1 => by cases H2 with | old_sem h2 => rw [h1] at h2; simp_all
  | .fresh_sem h1 => by cases H2 with | fresh_sem h2 => rw [h1] at h2; simp_all
  | .assigned_sem h1 => by cases H2 with | assigned_sem h2 => rw [h1] at h2; simp_all
  | .contract_of h1 => by cases H2 with | contract_of h2 => rw [h1] at h2; simp_all
  -- PrimitiveOp
  | .prim_op ha1 ho1 => by
      cases H2 with
      | prim_op ha2 ho2 =>
        have ⟨hha, hsa, hvs⟩ := EvalStmtArgs_deterministic ha1 ha2
        subst hha; subst hsa; subst hvs
        rw [ho1] at ho2; simp_all
  -- Single IH cases
  | .return_some Hv => by
      cases H2 with
      | return_some Hv2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Hv Hv2
        subst hh; subst hs; cases ho; exact ⟨rfl, rfl, rfl⟩
  | .assert_true _ => by cases H2 with | assert_true => exact ⟨rfl, rfl, rfl⟩
  | .assume_true _ => by cases H2 with | assume_true => exact ⟨rfl, rfl, rfl⟩
  | .prove_by Hv => by
      cases H2 with
      | prove_by Hv2 => exact EvalLaurelStmt_deterministic Hv Hv2
  | .as_type Ht => by
      cases H2 with
      | as_type Ht2 => exact EvalLaurelStmt_deterministic Ht Ht2
  -- Variable operations
  | .local_var_uninit Hn Hi => by
      cases H2 with
      | local_var_uninit _ Hi2 => exact ⟨rfl, InitStore_deterministic Hi Hi2, rfl⟩
  | .local_var_init Hv Hn Hi => by
      cases H2 with
      | local_var_init Hv2 _ Hi2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Hv Hv2
        subst hh; subst hs; cases ho
        exact ⟨rfl, InitStore_deterministic Hi Hi2, rfl⟩
  | .assign_single Hv Hm Hu => by
      cases H2 with
      | assign_single Hv2 _ Hu2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Hv Hv2
        subst hh; subst hs; cases ho
        exact ⟨rfl, UpdateStore_deterministic Hu Hu2, rfl⟩
  -- Heap: new_obj
  | .new_obj Ha => by
      cases H2 with
      | new_obj Ha2 =>
        have ⟨ha, hh⟩ := AllocHeap_deterministic Ha Ha2
        subst ha; subst hh; exact ⟨rfl, rfl, rfl⟩
  -- Conditionals (cross-case contradiction via bool determinism)
  | .ite_true Hc Ht => by
      cases H2 with
      | ite_true Hc2 Ht2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Hc Hc2
        subst hh; subst hs; cases ho
        exact EvalLaurelStmt_deterministic Ht Ht2
      | ite_false Hc2 _ =>
        have ⟨_, _, ho⟩ := EvalLaurelStmt_deterministic Hc Hc2; simp at ho
  | .ite_false Hc He => by
      cases H2 with
      | ite_true Hc2 _ =>
        have ⟨_, _, ho⟩ := EvalLaurelStmt_deterministic Hc Hc2; simp at ho
      | ite_false Hc2 He2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Hc Hc2
        subst hh; subst hs; cases ho
        exact EvalLaurelStmt_deterministic He He2
  | .ite_true_no_else Hc Ht => by
      cases H2 with
      | ite_true_no_else Hc2 Ht2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Hc Hc2
        subst hh; subst hs; cases ho
        exact EvalLaurelStmt_deterministic Ht Ht2
      | ite_false_no_else Hc2 =>
        have ⟨_, _, ho⟩ := EvalLaurelStmt_deterministic Hc Hc2; simp at ho
  | .ite_false_no_else Hc => by
      cases H2 with
      | ite_true_no_else Hc2 _ =>
        have ⟨_, _, ho⟩ := EvalLaurelStmt_deterministic Hc Hc2; simp at ho
      | ite_false_no_else Hc2 =>
        have ⟨hh, hs, _⟩ := EvalLaurelStmt_deterministic Hc Hc2
        subst hh; subst hs; exact ⟨rfl, rfl, rfl⟩
  -- Block
  | .block_sem Hb Hce => by
      cases H2 with
      | block_sem Hb2 Hce2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelBlock_deterministic Hb Hb2
        subst hh; subst hs; rw [ho] at Hce; rw [Hce] at Hce2
        exact ⟨rfl, rfl, Hce2⟩
  -- While loop (4 constructors × 4 cross-cases)
  | .while_true Hc Hb Hl => by
      cases H2 with
      | while_true Hc2 Hb2 Hl2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Hc Hc2
        subst hh; subst hs; cases ho
        have ⟨hh2, hs2, _⟩ := EvalLaurelStmt_deterministic Hb Hb2
        subst hh2; subst hs2
        exact EvalLaurelStmt_deterministic Hl Hl2
      | while_false Hc2 =>
        have ⟨_, _, ho⟩ := EvalLaurelStmt_deterministic Hc Hc2; simp at ho
      | while_exit Hc2 Hb2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Hc Hc2
        subst hh; subst hs; cases ho
        have ⟨_, _, ho2⟩ := EvalLaurelStmt_deterministic Hb Hb2; simp at ho2
      | while_return Hc2 Hb2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Hc Hc2
        subst hh; subst hs; cases ho
        have ⟨_, _, ho2⟩ := EvalLaurelStmt_deterministic Hb Hb2; simp at ho2
  | .while_false Hc => by
      cases H2 with
      | while_true Hc2 _ _ =>
        have ⟨_, _, ho⟩ := EvalLaurelStmt_deterministic Hc Hc2; simp at ho
      | while_false Hc2 =>
        have ⟨hh, hs, _⟩ := EvalLaurelStmt_deterministic Hc Hc2
        subst hh; subst hs; exact ⟨rfl, rfl, rfl⟩
      | while_exit Hc2 _ =>
        have ⟨_, _, ho⟩ := EvalLaurelStmt_deterministic Hc Hc2; simp at ho
      | while_return Hc2 _ =>
        have ⟨_, _, ho⟩ := EvalLaurelStmt_deterministic Hc Hc2; simp at ho
  | .while_exit Hc Hb => by
      cases H2 with
      | while_true Hc2 Hb2 _ =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Hc Hc2
        subst hh; subst hs; cases ho
        have ⟨_, _, ho2⟩ := EvalLaurelStmt_deterministic Hb Hb2; simp at ho2
      | while_false Hc2 =>
        have ⟨_, _, ho⟩ := EvalLaurelStmt_deterministic Hc Hc2; simp at ho
      | while_exit Hc2 Hb2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Hc Hc2
        subst hh; subst hs; cases ho
        exact EvalLaurelStmt_deterministic Hb Hb2
      | while_return Hc2 Hb2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Hc Hc2
        subst hh; subst hs; cases ho
        have ⟨_, _, ho2⟩ := EvalLaurelStmt_deterministic Hb Hb2; simp at ho2
  | .while_return Hc Hb => by
      cases H2 with
      | while_true Hc2 Hb2 _ =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Hc Hc2
        subst hh; subst hs; cases ho
        have ⟨_, _, ho2⟩ := EvalLaurelStmt_deterministic Hb Hb2; simp at ho2
      | while_false Hc2 =>
        have ⟨_, _, ho⟩ := EvalLaurelStmt_deterministic Hc Hc2; simp at ho
      | while_exit Hc2 Hb2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Hc Hc2
        subst hh; subst hs; cases ho
        have ⟨_, _, ho2⟩ := EvalLaurelStmt_deterministic Hb Hb2; simp at ho2
      | while_return Hc2 Hb2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Hc Hc2
        subst hh; subst hs; cases ho
        exact EvalLaurelStmt_deterministic Hb Hb2
  -- Static calls (3 constructors × 3 cross-cases, outcome discrimination)
  | .static_call Hp Ha Hb Hg Hbody => by
      cases H2 with
      | static_call Hp2 Ha2 Hb2 Hg2 Hbody2 =>
        rw [Hp] at Hp2; cases Hp2
        have ⟨hha, hsa, hvs⟩ := EvalStmtArgs_deterministic Ha Ha2
        subst hha; subst hsa; subst hvs
        rw [Hb] at Hb2; cases Hb2; rw [Hg] at Hg2; cases Hg2
        have ⟨hh, _, ho⟩ := EvalLaurelStmt_deterministic Hbody Hbody2
        subst hh; cases ho; exact ⟨rfl, rfl, rfl⟩
      | static_call_return Hp2 Ha2 Hb2 Hg2 Hbody2 =>
        rw [Hp] at Hp2; cases Hp2
        have ⟨hha, hsa, hvs⟩ := EvalStmtArgs_deterministic Ha Ha2
        subst hha; subst hsa; subst hvs
        rw [Hb] at Hb2; cases Hb2; rw [Hg] at Hg2; cases Hg2
        have ⟨_, _, ho⟩ := EvalLaurelStmt_deterministic Hbody Hbody2; simp at ho
      | static_call_return_void Hp2 Ha2 Hb2 Hg2 Hbody2 =>
        rw [Hp] at Hp2; cases Hp2
        have ⟨hha, hsa, hvs⟩ := EvalStmtArgs_deterministic Ha Ha2
        subst hha; subst hsa; subst hvs
        rw [Hb] at Hb2; cases Hb2; rw [Hg] at Hg2; cases Hg2
        have ⟨_, _, ho⟩ := EvalLaurelStmt_deterministic Hbody Hbody2; simp at ho
  | .static_call_return Hp Ha Hb Hg Hbody => by
      cases H2 with
      | static_call Hp2 Ha2 Hb2 Hg2 Hbody2 =>
        rw [Hp] at Hp2; cases Hp2
        have ⟨hha, hsa, hvs⟩ := EvalStmtArgs_deterministic Ha Ha2
        subst hha; subst hsa; subst hvs
        rw [Hb] at Hb2; cases Hb2; rw [Hg] at Hg2; cases Hg2
        have ⟨_, _, ho⟩ := EvalLaurelStmt_deterministic Hbody Hbody2; simp at ho
      | static_call_return Hp2 Ha2 Hb2 Hg2 Hbody2 =>
        rw [Hp] at Hp2; cases Hp2
        have ⟨hha, hsa, hvs⟩ := EvalStmtArgs_deterministic Ha Ha2
        subst hha; subst hsa; subst hvs
        rw [Hb] at Hb2; cases Hb2; rw [Hg] at Hg2; cases Hg2
        have ⟨hh, _, ho⟩ := EvalLaurelStmt_deterministic Hbody Hbody2
        subst hh; cases ho; exact ⟨rfl, rfl, rfl⟩
      | static_call_return_void Hp2 Ha2 Hb2 Hg2 Hbody2 =>
        rw [Hp] at Hp2; cases Hp2
        have ⟨hha, hsa, hvs⟩ := EvalStmtArgs_deterministic Ha Ha2
        subst hha; subst hsa; subst hvs
        rw [Hb] at Hb2; cases Hb2; rw [Hg] at Hg2; cases Hg2
        have ⟨_, _, ho⟩ := EvalLaurelStmt_deterministic Hbody Hbody2; simp at ho
  | .static_call_return_void Hp Ha Hb Hg Hbody => by
      cases H2 with
      | static_call Hp2 Ha2 Hb2 Hg2 Hbody2 =>
        rw [Hp] at Hp2; cases Hp2
        have ⟨hha, hsa, hvs⟩ := EvalStmtArgs_deterministic Ha Ha2
        subst hha; subst hsa; subst hvs
        rw [Hb] at Hb2; cases Hb2; rw [Hg] at Hg2; cases Hg2
        have ⟨_, _, ho⟩ := EvalLaurelStmt_deterministic Hbody Hbody2; simp at ho
      | static_call_return Hp2 Ha2 Hb2 Hg2 Hbody2 =>
        rw [Hp] at Hp2; cases Hp2
        have ⟨hha, hsa, hvs⟩ := EvalStmtArgs_deterministic Ha Ha2
        subst hha; subst hsa; subst hvs
        rw [Hb] at Hb2; cases Hb2; rw [Hg] at Hg2; cases Hg2
        have ⟨_, _, ho⟩ := EvalLaurelStmt_deterministic Hbody Hbody2; simp at ho
      | static_call_return_void Hp2 Ha2 Hb2 Hg2 Hbody2 =>
        rw [Hp] at Hp2; cases Hp2
        have ⟨hha, hsa, hvs⟩ := EvalStmtArgs_deterministic Ha Ha2
        subst hha; subst hsa; subst hvs
        rw [Hb] at Hb2; cases Hb2; rw [Hg] at Hg2; cases Hg2
        have ⟨hh, _, ho⟩ := EvalLaurelStmt_deterministic Hbody Hbody2
        subst hh; cases ho; exact ⟨rfl, rfl, rfl⟩
  -- OO: field_select, pure_field_update, reference_equals, assign_field
  | .field_select Ht Hr => by
      cases H2 with
      | field_select Ht2 Hr2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Ht Ht2
        subst hh; subst hs; cases ho
        rw [Hr] at Hr2; cases Hr2; exact ⟨rfl, rfl, rfl⟩
  | .pure_field_update Ht Hv Hw => by
      cases H2 with
      | pure_field_update Ht2 Hv2 Hw2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Ht Ht2
        subst hh; subst hs; cases ho
        have ⟨hh2, hs2, ho2⟩ := EvalLaurelStmt_deterministic Hv Hv2
        subst hh2; subst hs2; cases ho2
        exact ⟨HeapFieldWrite_deterministic Hw Hw2, rfl, rfl⟩
  | .reference_equals Hl Hr => by
      cases H2 with
      | reference_equals Hl2 Hr2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Hl Hl2
        subst hh; subst hs; cases ho
        have ⟨hh2, hs2, ho2⟩ := EvalLaurelStmt_deterministic Hr Hr2
        subst hh2; subst hs2; cases ho2; exact ⟨rfl, rfl, rfl⟩
  | .assign_field Ht Hv Hw => by
      cases H2 with
      | assign_field Ht2 Hv2 Hw2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Ht Ht2
        subst hh; subst hs; cases ho
        have ⟨hh2, hs2, ho2⟩ := EvalLaurelStmt_deterministic Hv Hv2
        subst hh2; subst hs2; cases ho2
        exact ⟨HeapFieldWrite_deterministic Hw Hw2, rfl, rfl⟩
  -- OO: is_type
  | .is_type Ht Hlook => by
      cases H2 with
      | is_type Ht2 Hlook2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Ht Ht2
        subst hh; subst hs; cases ho
        rw [Hlook] at Hlook2; cases Hlook2; exact ⟨rfl, rfl, rfl⟩
  -- Instance calls (3 constructors × 3 cross-cases)
  | .instance_call Ht Hlook Hp Ha Hb Hg Hbody => by
      cases H2 with
      | instance_call Ht2 Hlook2 Hp2 Ha2 Hb2 Hg2 Hbody2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Ht Ht2
        subst hh; subst hs; cases ho
        rw [Hlook] at Hlook2; cases Hlook2; rw [Hp] at Hp2; cases Hp2
        have ⟨hha, hsa, hvs⟩ := EvalStmtArgs_deterministic Ha Ha2
        subst hha; subst hsa; subst hvs
        rw [Hb] at Hb2; cases Hb2; rw [Hg] at Hg2; cases Hg2
        have ⟨hh2, _, ho2⟩ := EvalLaurelStmt_deterministic Hbody Hbody2
        subst hh2; cases ho2; exact ⟨rfl, rfl, rfl⟩
      | instance_call_return Ht2 Hlook2 Hp2 Ha2 Hb2 Hg2 Hbody2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Ht Ht2
        subst hh; subst hs; cases ho
        rw [Hlook] at Hlook2; cases Hlook2; rw [Hp] at Hp2; cases Hp2
        have ⟨hha, hsa, hvs⟩ := EvalStmtArgs_deterministic Ha Ha2
        subst hha; subst hsa; subst hvs
        rw [Hb] at Hb2; cases Hb2; rw [Hg] at Hg2; cases Hg2
        have ⟨_, _, ho2⟩ := EvalLaurelStmt_deterministic Hbody Hbody2; simp at ho2
      | instance_call_return_void Ht2 Hlook2 Hp2 Ha2 Hb2 Hg2 Hbody2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Ht Ht2
        subst hh; subst hs; cases ho
        rw [Hlook] at Hlook2; cases Hlook2; rw [Hp] at Hp2; cases Hp2
        have ⟨hha, hsa, hvs⟩ := EvalStmtArgs_deterministic Ha Ha2
        subst hha; subst hsa; subst hvs
        rw [Hb] at Hb2; cases Hb2; rw [Hg] at Hg2; cases Hg2
        have ⟨_, _, ho2⟩ := EvalLaurelStmt_deterministic Hbody Hbody2; simp at ho2
  | .instance_call_return Ht Hlook Hp Ha Hb Hg Hbody => by
      cases H2 with
      | instance_call Ht2 Hlook2 Hp2 Ha2 Hb2 Hg2 Hbody2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Ht Ht2
        subst hh; subst hs; cases ho
        rw [Hlook] at Hlook2; cases Hlook2; rw [Hp] at Hp2; cases Hp2
        have ⟨hha, hsa, hvs⟩ := EvalStmtArgs_deterministic Ha Ha2
        subst hha; subst hsa; subst hvs
        rw [Hb] at Hb2; cases Hb2; rw [Hg] at Hg2; cases Hg2
        have ⟨_, _, ho2⟩ := EvalLaurelStmt_deterministic Hbody Hbody2; simp at ho2
      | instance_call_return Ht2 Hlook2 Hp2 Ha2 Hb2 Hg2 Hbody2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Ht Ht2
        subst hh; subst hs; cases ho
        rw [Hlook] at Hlook2; cases Hlook2; rw [Hp] at Hp2; cases Hp2
        have ⟨hha, hsa, hvs⟩ := EvalStmtArgs_deterministic Ha Ha2
        subst hha; subst hsa; subst hvs
        rw [Hb] at Hb2; cases Hb2; rw [Hg] at Hg2; cases Hg2
        have ⟨hh2, _, ho2⟩ := EvalLaurelStmt_deterministic Hbody Hbody2
        subst hh2; cases ho2; exact ⟨rfl, rfl, rfl⟩
      | instance_call_return_void Ht2 Hlook2 Hp2 Ha2 Hb2 Hg2 Hbody2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Ht Ht2
        subst hh; subst hs; cases ho
        rw [Hlook] at Hlook2; cases Hlook2; rw [Hp] at Hp2; cases Hp2
        have ⟨hha, hsa, hvs⟩ := EvalStmtArgs_deterministic Ha Ha2
        subst hha; subst hsa; subst hvs
        rw [Hb] at Hb2; cases Hb2; rw [Hg] at Hg2; cases Hg2
        have ⟨_, _, ho2⟩ := EvalLaurelStmt_deterministic Hbody Hbody2; simp at ho2
  | .instance_call_return_void Ht Hlook Hp Ha Hb Hg Hbody => by
      cases H2 with
      | instance_call Ht2 Hlook2 Hp2 Ha2 Hb2 Hg2 Hbody2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Ht Ht2
        subst hh; subst hs; cases ho
        rw [Hlook] at Hlook2; cases Hlook2; rw [Hp] at Hp2; cases Hp2
        have ⟨hha, hsa, hvs⟩ := EvalStmtArgs_deterministic Ha Ha2
        subst hha; subst hsa; subst hvs
        rw [Hb] at Hb2; cases Hb2; rw [Hg] at Hg2; cases Hg2
        have ⟨_, _, ho2⟩ := EvalLaurelStmt_deterministic Hbody Hbody2; simp at ho2
      | instance_call_return Ht2 Hlook2 Hp2 Ha2 Hb2 Hg2 Hbody2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Ht Ht2
        subst hh; subst hs; cases ho
        rw [Hlook] at Hlook2; cases Hlook2; rw [Hp] at Hp2; cases Hp2
        have ⟨hha, hsa, hvs⟩ := EvalStmtArgs_deterministic Ha Ha2
        subst hha; subst hsa; subst hvs
        rw [Hb] at Hb2; cases Hb2; rw [Hg] at Hg2; cases Hg2
        have ⟨_, _, ho2⟩ := EvalLaurelStmt_deterministic Hbody Hbody2; simp at ho2
      | instance_call_return_void Ht2 Hlook2 Hp2 Ha2 Hb2 Hg2 Hbody2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic Ht Ht2
        subst hh; subst hs; cases ho
        rw [Hlook] at Hlook2; cases Hlook2; rw [Hp] at Hp2; cases Hp2
        have ⟨hha, hsa, hvs⟩ := EvalStmtArgs_deterministic Ha Ha2
        subst hha; subst hsa; subst hvs
        rw [Hb] at Hb2; cases Hb2; rw [Hg] at Hg2; cases Hg2
        have ⟨hh2, _, ho2⟩ := EvalLaurelStmt_deterministic Hbody Hbody2
        subst hh2; cases ho2; exact ⟨rfl, rfl, rfl⟩

theorem EvalStmtArgs_deterministic
    {δ : LaurelEval} {π : ProcEnv} {h : LaurelHeap} {σ : LaurelStore}
    {es : List StmtExprMd} {h₁ h₂ : LaurelHeap} {σ₁ σ₂ : LaurelStore}
    {vs₁ vs₂ : List LaurelValue}
    (H1 : EvalStmtArgs δ π h σ es h₁ σ₁ vs₁)
    (H2 : EvalStmtArgs δ π h σ es h₂ σ₂ vs₂) :
    h₁ = h₂ ∧ σ₁ = σ₂ ∧ vs₁ = vs₂ :=
  match H1 with
  | .nil => by cases H2; exact ⟨rfl, rfl, rfl⟩
  | .cons He Ht => by
      cases H2 with
      | cons He2 Ht2 =>
        have ⟨hh, hs, ho⟩ := EvalLaurelStmt_deterministic He He2
        subst hh; subst hs; cases ho
        have ⟨hh2, hs2, hvs⟩ := EvalStmtArgs_deterministic Ht Ht2
        subst hh2; subst hs2; subst hvs
        exact ⟨rfl, rfl, rfl⟩

theorem EvalLaurelBlock_deterministic
    {δ : LaurelEval} {π : ProcEnv} {h : LaurelHeap} {σ : LaurelStore}
    {ss : List StmtExprMd} {h₁ h₂ : LaurelHeap} {σ₁ σ₂ : LaurelStore} {o₁ o₂ : Outcome}
    (H1 : EvalLaurelBlock δ π h σ ss h₁ σ₁ o₁)
    (H2 : EvalLaurelBlock δ π h σ ss h₂ σ₂ o₂) :
    h₁ = h₂ ∧ σ₁ = σ₂ ∧ o₁ = o₂ :=
  match H1 with
  | .nil => by cases H2; exact ⟨rfl, rfl, rfl⟩
  | .last_normal Hs => by
      cases H2 with
      | last_normal Hs2 => exact EvalLaurelStmt_deterministic Hs Hs2
      | cons_normal Hs2 Hne _ => exact absurd rfl Hne
      | cons_exit Hs2 =>
        have ⟨_, _, ho⟩ := EvalLaurelStmt_deterministic Hs Hs2; simp at ho
      | cons_return Hs2 =>
        have ⟨_, _, ho⟩ := EvalLaurelStmt_deterministic Hs Hs2; simp at ho
  | .cons_normal Hs Hne Hr => by
      cases H2 with
      | last_normal Hs2 => exact absurd rfl Hne
      | cons_normal Hs2 _ Hr2 =>
        have ⟨hh, hs, _⟩ := EvalLaurelStmt_deterministic Hs Hs2
        subst hh; subst hs
        exact EvalLaurelBlock_deterministic Hr Hr2
      | cons_exit Hs2 =>
        have ⟨_, _, ho⟩ := EvalLaurelStmt_deterministic Hs Hs2; simp at ho
      | cons_return Hs2 =>
        have ⟨_, _, ho⟩ := EvalLaurelStmt_deterministic Hs Hs2; simp at ho
  | .cons_exit Hs => by
      cases H2 with
      | last_normal Hs2 =>
        have ⟨_, _, ho⟩ := EvalLaurelStmt_deterministic Hs Hs2; simp at ho
      | cons_normal Hs2 _ _ =>
        have ⟨_, _, ho⟩ := EvalLaurelStmt_deterministic Hs Hs2; simp at ho
      | cons_exit Hs2 => exact EvalLaurelStmt_deterministic Hs Hs2
      | cons_return Hs2 =>
        have ⟨_, _, ho⟩ := EvalLaurelStmt_deterministic Hs Hs2; simp at ho
  | .cons_return Hs => by
      cases H2 with
      | last_normal Hs2 =>
        have ⟨_, _, ho⟩ := EvalLaurelStmt_deterministic Hs Hs2; simp at ho
      | cons_normal Hs2 _ _ =>
        have ⟨_, _, ho⟩ := EvalLaurelStmt_deterministic Hs Hs2; simp at ho
      | cons_exit Hs2 =>
        have ⟨_, _, ho⟩ := EvalLaurelStmt_deterministic Hs Hs2; simp at ho
      | cons_return Hs2 => exact EvalLaurelStmt_deterministic Hs Hs2
end

/-! ## Store Operation Lemmas -/

/-- InitStore on a fresh name preserves existing variable values. -/
theorem InitStore_get_other {σ σ' : LaurelStore} {x y : Identifier} {v : LaurelValue}
    (hinit : InitStore σ x v σ') (hne : x ≠ y) :
    σ' y = σ y := by
  cases hinit with | init _ _ hrest => exact hrest y hne

/-- UpdateStore preserves values of other variables. -/
theorem UpdateStore_get_other {σ σ' : LaurelStore} {x y : Identifier} {v : LaurelValue}
    (hup : UpdateStore σ x v σ') (hne : x ≠ y) :
    σ' y = σ y := by
  cases hup with | update _ _ hrest => exact hrest y hne

/-- UpdateStore sets the target variable. -/
theorem UpdateStore_get_self {σ σ' : LaurelStore} {x : Identifier} {v : LaurelValue}
    (hup : UpdateStore σ x v σ') :
    σ' x = some v := by
  cases hup with | update _ hnew _ => exact hnew

/-- InitStore sets the target variable. -/
theorem InitStore_get_self {σ σ' : LaurelStore} {x : Identifier} {v : LaurelValue}
    (hinit : InitStore σ x v σ') :
    σ' x = some v := by
  cases hinit with | init _ hnew _ => exact hnew

/-! ## Block Append Lemma -/

/-- Evaluating a block `[s] ++ rest` where `s` produces `.normal` is equivalent to
evaluating `s`, then evaluating `rest` in the resulting state. -/
theorem EvalLaurelBlock_cons_normal_append
    {δ : LaurelEval} {π : ProcEnv} {h : LaurelHeap} {σ : LaurelStore}
    {s : StmtExprMd} {rest : List StmtExprMd}
    {h₁ : LaurelHeap} {σ₁ : LaurelStore} {v : LaurelValue}
    {h₂ : LaurelHeap} {σ₂ : LaurelStore} {o : Outcome}
    (hs : EvalLaurelStmt δ π h σ s h₁ σ₁ (.normal v))
    (hne : rest ≠ [])
    (hrest : EvalLaurelBlock δ π h₁ σ₁ rest h₂ σ₂ o) :
    EvalLaurelBlock δ π h σ (s :: rest) h₂ σ₂ o :=
  .cons_normal hs hne hrest

/-! ## Block Value Semantics -/

theorem empty_block_void :
    EvalLaurelBlock δ π h σ [] h σ (.normal .vVoid) :=
  EvalLaurelBlock.nil

theorem singleton_block_value :
    EvalLaurelStmt δ π h σ s h' σ' (.normal v) →
    EvalLaurelBlock δ π h σ [s] h' σ' (.normal v) :=
  EvalLaurelBlock.last_normal

/-! ## Block Append -/

/-- Evaluating `ss₁ ++ ss₂` where `ss₁` produces `.normal` is equivalent to
evaluating `ss₁`, then evaluating `ss₂` in the resulting state.
This is the key composition lemma for the lifting correctness proof. -/
theorem EvalLaurelBlock_append
    {δ : LaurelEval} {π : ProcEnv}
    {h : LaurelHeap} {σ : LaurelStore}
    {ss₁ ss₂ : List StmtExprMd}
    {h₁ : LaurelHeap} {σ₁ : LaurelStore} {v₁ : LaurelValue}
    {h₂ : LaurelHeap} {σ₂ : LaurelStore} {o₂ : Outcome}
    (hss₁ : EvalLaurelBlock δ π h σ ss₁ h₁ σ₁ (.normal v₁))
    (hne : ss₂ ≠ [])
    (hss₂ : EvalLaurelBlock δ π h₁ σ₁ ss₂ h₂ σ₂ o₂) :
    EvalLaurelBlock δ π h σ (ss₁ ++ ss₂) h₂ σ₂ o₂ := by
  match hss₁ with
  | .nil =>
    -- ss₁ = [], so ss₁ ++ ss₂ = ss₂
    exact hss₂
  | .last_normal hs =>
    -- ss₁ = [s], so ss₁ ++ ss₂ = s :: ss₂
    exact .cons_normal hs hne hss₂
  | .cons_normal hs hne_rest hrest =>
    -- ss₁ = s :: rest, rest ≠ []
    simp only [List.cons_append]
    exact .cons_normal hs
      (by simp [List.append_eq_nil_iff, hne_rest])
      (EvalLaurelBlock_append hrest hne hss₂)

/-- Variant of `EvalLaurelBlock_append` where `ss₂` is a singleton. -/
theorem EvalLaurelBlock_append_singleton
    {δ : LaurelEval} {π : ProcEnv}
    {h : LaurelHeap} {σ : LaurelStore}
    {ss₁ : List StmtExprMd} {s₂ : StmtExprMd}
    {h₁ : LaurelHeap} {σ₁ : LaurelStore} {v₁ : LaurelValue}
    {h₂ : LaurelHeap} {σ₂ : LaurelStore} {o₂ : Outcome}
    (hss₁ : EvalLaurelBlock δ π h σ ss₁ h₁ σ₁ (.normal v₁))
    (hs₂ : EvalLaurelStmt δ π h₁ σ₁ s₂ h₂ σ₂ o₂) :
    EvalLaurelBlock δ π h σ (ss₁ ++ [s₂]) h₂ σ₂ o₂ := by
  cases o₂ with
  | normal v₂ =>
    exact EvalLaurelBlock_append hss₁ (by simp) (.last_normal hs₂)
  | exit label =>
    exact EvalLaurelBlock_append hss₁ (by simp) (.cons_exit hs₂)
  | ret rv =>
    exact EvalLaurelBlock_append hss₁ (by simp) (.cons_return hs₂)

/-- Splitting `EvalStmtArgs` at a point: if we evaluate `[a] ++ rest`,
we can decompose into evaluating `a` then `rest`. -/
theorem EvalStmtArgs_cons_inv
    {δ : LaurelEval} {π : ProcEnv}
    {h : LaurelHeap} {σ : LaurelStore}
    {e : StmtExprMd} {es : List StmtExprMd}
    {h' : LaurelHeap} {σ' : LaurelStore}
    {vs : List LaurelValue}
    (heval : EvalStmtArgs δ π h σ (e :: es) h' σ' vs) :
    ∃ v h₁ σ₁ vs',
      vs = v :: vs' ∧
      EvalLaurelStmt δ π h σ e h₁ σ₁ (.normal v) ∧
      EvalStmtArgs δ π h₁ σ₁ es h' σ' vs' := by
  cases heval with
  | cons he hrest => exact ⟨_, _, _, _, rfl, he, hrest⟩

end Strata.Laurel
