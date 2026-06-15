/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.CFGSemantics
public import Strata.Transform.StructuredToUnstructuredCorrect
public import Strata.Transform.LoopInitHoistRewrite
import all Strata.DL.Imperative.Cmd

/-! # Loop-init hoisting: equivalence infrastructure

This file collects the load-bearing equivalence lemmas used by the loop-init
hoisting correctness proof. The pass transforms a structured program so that
every `.loop` body satisfies `Block.initVars body = []`; the proofs in this
file justify the rewriting piecewise.

The live infrastructure is:

- `HoistInv` — the guarded forward-simulation store relation between the source
  and hoisted runs (modulo the fresh hoisted variables), with its transports
  (`refl_id`, `to_storeAgreement_nil`, `extend_both_outside_subst`,
  `set_both_in_subst`, `project_both`, `add_vacuous_pairs`).
- `substFvarMany` / `renameLookup` — the simultaneous renaming the lift applies,
  plus the expression-level transport `substFvarMany_eval_tweak`.
- `extendStoreMany`, `projectStore_undef_at`, `read_vars_def_of_eval`,
  `stmts_cons_terminal_inv` — the store/run helpers the prelude and loop
  drivers consume.
-/

public section

namespace Imperative

variable {P : PureExpr}

/-! ## Store helper: `projectStore` reverts to `none` on parent-undefined keys -/

open StructuredToUnstructuredCorrect (EvalCmds)
private theorem projectStore_undef_at {P : PureExpr}
    {σ_parent σ_inner : SemanticStore P} {x : P.Ident}
    (h : σ_parent x = none) :
    projectStore σ_parent σ_inner x = none := by
  unfold projectStore
  simp [h]

/-- Guarded HoistInv invariant for the fresh-name hoist pass.

Component (1) — FRAME: outside `A ∪ B`, stores agree pointwise.
Component (2) — GUARDED PAIRWISE: source-defined ⇒ hoist-defined-and-equal.

The `σ_src a ≠ none` antecedent absorbs the timing asymmetry between
source's per-iteration `step_block_done` projection (which pops body-locals
to `none`) and hoist's outer-scope persistence (where the prelude havoc
keeps the renamed slot defined).  When source pops, antecedent fails,
component (2) is vacuously preserved. -/
@[expose] def HoistInv {P : PureExpr}
    (A B : List P.Ident)
    (subst : List (P.Ident × P.Ident))
    (σ_src σ_h : SemanticStore P) : Prop :=
  (∀ x : P.Ident, x ∉ A → x ∉ B → σ_src x ≠ none → σ_src x = σ_h x)
  ∧
  (∀ a b : P.Ident, (a, b) ∈ subst →
      σ_src a ≠ none → (σ_h b ≠ none ∧ σ_src a = σ_h b))

/-- Auxiliary: membership in `A.zip A` forces equality of the components. -/
private theorem mem_zip_self_eq {P : PureExpr}
    {A : List P.Ident} {a b : P.Ident}
    (h : (a, b) ∈ A.zip A) : a = b := by
  induction A with
  | nil => simp [List.zip, List.zipWith] at h
  | cons hd tl ih =>
    rw [List.zip, List.zipWith] at h
    rcases List.mem_cons.mp h with h_eq | h_in
    · cases h_eq; rfl
    · exact ih h_in

/-- Reflexivity (identity-subst form): when `subst = A.zip A` and `σ_src = σ_h`,
`HoistInv A A (A.zip A) σ σ` holds.  The frame component is `rfl`; the
guarded pairwise reduces to `σ a ≠ none → σ a = σ a`. -/
theorem HoistInv.refl_id {P : PureExpr}
    (A : List P.Ident) (σ : SemanticStore P) :
    HoistInv (P := P) A A (A.zip A) σ σ := by
  refine ⟨fun _ _ _ _ => rfl, ?_⟩
  intro a b h_pair h_ne
  have h_ab : a = b := mem_zip_self_eq h_pair
  subst h_ab
  exact ⟨h_ne, rfl⟩

/-- Forward-simulation bridge: `HoistInv A B subst σ_src σ_h` plus
    (a) every `A`-var undefined in `σ_src`,
    (b) every `B`-var undefined in `σ_src`,
    (c) every source-side `subst` key lying in `A`,
    yields `StoreAgreement σ_src σ_h` — the conventional source-on-left
    forward-simulation store relation (CmdSemantics).

The bridge constrains only source-defined variables: a variable `x` defined in
`σ_src` cannot be in `A` or `B` (both undefined there), so the unconditional
frame component (1) of `HoistInv` delivers `σ_src x = σ_h x` directly. The fresh
hoist carriers (`A`/`B`) and projected loop-locals stay correctly unconstrained.
The reverse direction is intentionally NOT claimed; `StoreAgreement` is strictly
weaker (it says nothing at undefined source vars), which is exactly why it is the
sound end-to-end conclusion. -/
theorem HoistInv.to_storeAgreement {P : PureExpr} [DecidableEq P.Ident]
    {A B : List P.Ident}
    {subst : List (P.Ident × P.Ident)}
    {σ_src σ_h : SemanticStore P}
    (h : HoistInv (P := P) A B subst σ_src σ_h)
    (h_A_undef : ∀ a ∈ A, σ_src a = none)
    (h_B_undef : ∀ b ∈ B, σ_src b = none)
    (_h_subst_src_in_A : ∀ a ∈ subst.map Prod.fst, a ∈ A) :
    StoreAgreement σ_src σ_h := by
  intro x h_def
  have h_x_some : (σ_src x).isSome = true := h_def x (List.mem_singleton.mpr rfl)
  have h_x_ne : σ_src x ≠ none := by
    intro h_none; rw [h_none] at h_x_some; simp at h_x_some
  have h_x_notA : x ∉ A := fun hxA => h_x_ne (h_A_undef x hxA)
  have h_x_notB : x ∉ B := fun hxB => h_x_ne (h_B_undef x hxB)
  exact h.1 x h_x_notA h_x_notB h_x_ne

/-- §F-specialized bridge: at `A = B = subst = []` the side-premises are vacuous,
so `HoistInv [] [] [] σ_src σ_h → StoreAgreement σ_src σ_h` unconditionally. This
is exactly the step §F needs in place of the (false) `∀ x, σ_h x = σ_src x`. -/
theorem HoistInv.to_storeAgreement_nil {P : PureExpr} [DecidableEq P.Ident]
    {σ_src σ_h : SemanticStore P}
    (h : HoistInv (P := P) [] [] [] σ_src σ_h) :
    StoreAgreement σ_src σ_h :=
  HoistInv.to_storeAgreement h
    (fun _ hc => absurd hc List.not_mem_nil)
    (fun _ hc => absurd hc List.not_mem_nil)
    (fun _ hc => absurd hc List.not_mem_nil)

/-- Transport: parallel update at `x ∉ A ∪ B` preserves both components.

Requires the well-formedness hypothesis that every `subst` pair has its
source side in `A` and hoist side in `B`.  Combined with `x ∉ A` and
`x ∉ B`, this gives `a ≠ x ∧ b ≠ x` for every pair, so the extension
at `x` misses both sides of every pair. -/
theorem HoistInv.extend_both_outside_subst {P : PureExpr} [DecidableEq P.Ident]
    {A B : List P.Ident}
    {subst : List (P.Ident × P.Ident)}
    {σ_src σ_h : SemanticStore P}
    {x : P.Ident} {v : P.Expr}
    (h_x_notin_A : x ∉ A) (h_x_notin_B : x ∉ B)
    (h_subst_wf : ∀ a b, (a, b) ∈ subst → a ∈ A ∧ b ∈ B)
    (h : HoistInv (P := P) A B subst σ_src σ_h) :
    HoistInv (P := P) A B subst
      (StructuredToUnstructuredCorrect.extendStoreOne σ_src x v)
      (StructuredToUnstructuredCorrect.extendStoreOne σ_h x v) := by
  refine ⟨?_, ?_⟩
  · intro y h_y_notin_A h_y_notin_B h_y_ne
    by_cases hyx : y = x
    · subst hyx
      rw [StructuredToUnstructuredCorrect.extendStoreOne_self σ_src y v,
          StructuredToUnstructuredCorrect.extendStoreOne_self σ_h y v]
    · rw [StructuredToUnstructuredCorrect.extendStoreOne_other σ_src x v y hyx] at h_y_ne
      rw [StructuredToUnstructuredCorrect.extendStoreOne_other σ_src x v y hyx,
          StructuredToUnstructuredCorrect.extendStoreOne_other σ_h x v y hyx]
      exact h.1 y h_y_notin_A h_y_notin_B h_y_ne
  · intro a b h_pair h_src_ne
    have h_wf := h_subst_wf a b h_pair
    have h_a_in_A : a ∈ A := h_wf.1
    have h_b_in_B : b ∈ B := h_wf.2
    have hax : a ≠ x := fun heq => h_x_notin_A (heq ▸ h_a_in_A)
    have hbx : b ≠ x := fun heq => h_x_notin_B (heq ▸ h_b_in_B)
    rw [StructuredToUnstructuredCorrect.extendStoreOne_other σ_src x v a hax] at h_src_ne
    have h_old := h.2 a b h_pair h_src_ne
    rw [StructuredToUnstructuredCorrect.extendStoreOne_other σ_src x v a hax,
        StructuredToUnstructuredCorrect.extendStoreOne_other σ_h x v b hbx]
    exact h_old

/-! ## Phase 8 Option F — Critical lemmas

Load-bearing `HoistInv` transports: `extend_both_outside_subst` and
`set_both_in_subst` (parallel update at a non-carrier resp. a renamed slot),
`project_both` (body-exit projection), and `add_vacuous_pairs`. -/

/-- The body's parallel-update step.  Source `init`s `a` (was undef, becomes
`some v`); hoist `set`s `b` (was defined, becomes `some v`).  Antecedent of
component (2) flips from FALSE to TRUE; both clauses must hold post-update. -/
theorem HoistInv.set_both_in_subst {P : PureExpr} [DecidableEq P.Ident]
    {A B : List P.Ident}
    {subst : List (P.Ident × P.Ident)}
    {σ_src σ_h : SemanticStore P}
    {a b : P.Ident} {v : P.Expr}
    (h_pair : (a, b) ∈ subst)
    (h_in_A : a ∈ A) (h_in_B : b ∈ B)
    (h_unique_a : ∀ a' b', (a', b') ∈ subst → a' = a → b' = b)
    (h_unique_b : ∀ a' b', (a', b') ∈ subst → b' = b → a' = a)
    (h : HoistInv (P := P) A B subst σ_src σ_h) :
    HoistInv (P := P) A B subst
      (StructuredToUnstructuredCorrect.extendStoreOne σ_src a v)
      (StructuredToUnstructuredCorrect.extendStoreOne σ_h b v) := by
  refine ⟨?_, ?_⟩
  · -- Component 1: outside A ∪ B.  Since a ∈ A and b ∈ B, neither extension
    -- touches a key outside A ∪ B.
    intro x h_x_notin_A h_x_notin_B h_x_ne
    have hxa : x ≠ a := fun heq => h_x_notin_A (heq ▸ h_in_A)
    have hxb : x ≠ b := fun heq => h_x_notin_B (heq ▸ h_in_B)
    rw [StructuredToUnstructuredCorrect.extendStoreOne_other σ_src a v x hxa] at h_x_ne
    rw [StructuredToUnstructuredCorrect.extendStoreOne_other σ_src a v x hxa,
        StructuredToUnstructuredCorrect.extendStoreOne_other σ_h b v x hxb]
    exact h.1 x h_x_notin_A h_x_notin_B h_x_ne
  · -- Component 2: subst pair (a', b') with σ_src-ext a' ≠ none.
    intro a' b' h_pair' h_src_ne
    by_cases ha'a : a' = a
    · -- Case a' = a: by uniqueness, b' = b.
      have hb'b : b' = b := h_unique_a a' b' h_pair' ha'a
      subst ha'a
      subst hb'b
      refine ⟨?_, ?_⟩
      · rw [StructuredToUnstructuredCorrect.extendStoreOne_self σ_h b' v]
        intro h_eq; cases h_eq
      · rw [StructuredToUnstructuredCorrect.extendStoreOne_self σ_src a' v,
            StructuredToUnstructuredCorrect.extendStoreOne_self σ_h b' v]
    · -- Case a' ≠ a: σ_src-ext a' = σ_src a'.
      have h_src_ne' : σ_src a' ≠ none := by
        rw [StructuredToUnstructuredCorrect.extendStoreOne_other σ_src a v a' ha'a] at h_src_ne
        exact h_src_ne
      have h_old := h.2 a' b' h_pair' h_src_ne'
      have hb'b : b' ≠ b := by
        intro heq
        exact ha'a (h_unique_b a' b' h_pair' heq)
      refine ⟨?_, ?_⟩
      · rw [StructuredToUnstructuredCorrect.extendStoreOne_other σ_h b v b' hb'b]
        exact h_old.1
      · rw [StructuredToUnstructuredCorrect.extendStoreOne_other σ_src a v a' ha'a,
            StructuredToUnstructuredCorrect.extendStoreOne_other σ_h b v b' hb'b]
        exact h_old.2

/-- Both-sides projection: the body-exit `projectStore` operation applied
in parallel to source and hoist preserves `HoistInv`.  This is the
HoistInv analog of `projectStore_iter_agree`.

For the existing pass (where the source-side hoist names are NOT in
`Block.initVars` of the body, so component (2) at iteration boundaries
is preserved), the parent's HoistInv suffices to lift through the
projection: if `parent_src` and `parent_hoist` agree under HoistInv
and `inner_src` and `inner_hoist` agree under HoistInv, then the
projected pair also agrees under HoistInv. -/
theorem HoistInv.project_both {P : PureExpr} [DecidableEq P.Ident]
    {A B : List P.Ident}
    {subst : List (P.Ident × P.Ident)}
    {parent_src parent_hoist inner_src inner_hoist : SemanticStore P}
    (h_parent : HoistInv (P := P) A B subst parent_src parent_hoist)
    (h_inner : HoistInv (P := P) A B subst inner_src inner_hoist) :
    HoistInv (P := P) A B subst
      (projectStore parent_src inner_src)
      (projectStore parent_hoist inner_hoist) := by
  refine ⟨?_, ?_⟩
  · -- Component 1: outside A ∪ B, both projected stores agree.  The guard
    -- `h_x_ne` forces `(parent_src x).isSome` and `inner_src x ≠ none`, which
    -- discharge the guards of `h_parent.1`/`h_inner.1`.
    intro x h_x_notin_A h_x_notin_B h_x_ne
    have h_parent_src_some : (parent_src x).isSome = true := by
      unfold projectStore at h_x_ne
      by_cases h : (parent_src x).isSome
      · exact h
      · simp [h] at h_x_ne
    have h_parent_src_ne : parent_src x ≠ none := by
      intro h; rw [h] at h_parent_src_some; simp at h_parent_src_some
    have h_inner_src_ne : inner_src x ≠ none := by
      intro h_eq; unfold projectStore at h_x_ne
      rw [h_parent_src_some] at h_x_ne; simp at h_x_ne; exact h_x_ne h_eq
    have h_parent_eq := h_parent.1 x h_x_notin_A h_x_notin_B h_parent_src_ne
    have h_inner_eq := h_inner.1 x h_x_notin_A h_x_notin_B h_inner_src_ne
    unfold projectStore
    rw [h_parent_eq, h_inner_eq]
  · -- Component 2: for (a, b) ∈ subst, projected_src a ≠ none implies
    -- projected_hoist b ≠ none and they're equal.
    intro a b h_pair h_src_ne
    -- projectStore parent_src inner_src a = if (parent_src a).isSome then inner_src a else none
    -- src_ne ⇒ (parent_src a).isSome ∧ inner_src a is some.
    have h_parent_a_some : (parent_src a).isSome = true := by
      unfold projectStore at h_src_ne
      by_cases h : (parent_src a).isSome
      · exact h
      · simp [h] at h_src_ne
    have h_inner_a_ne : inner_src a ≠ none := by
      intro h_eq
      unfold projectStore at h_src_ne
      rw [h_parent_a_some] at h_src_ne
      simp at h_src_ne
      exact h_src_ne h_eq
    -- From parent: parent_src a ≠ none ⇒ parent_hoist b ≠ none ∧ parent_src a = parent_hoist b.
    have h_parent_a_ne : parent_src a ≠ none := by
      intro h
      rw [h] at h_parent_a_some
      simp at h_parent_a_some
    obtain ⟨h_parent_b_ne, h_parent_eq⟩ := h_parent.2 a b h_pair h_parent_a_ne
    -- From inner: inner_src a ≠ none ⇒ inner_hoist b ≠ none ∧ inner_src a = inner_hoist b.
    obtain ⟨h_inner_b_ne, h_inner_eq⟩ := h_inner.2 a b h_pair h_inner_a_ne
    -- projected_hoist b = (if (parent_hoist b).isSome then inner_hoist b else none) = inner_hoist b.
    have h_parent_b_some : (parent_hoist b).isSome = true := by
      cases h : parent_hoist b with
      | none => exact absurd h h_parent_b_ne
      | some _ => rfl
    refine ⟨?_, ?_⟩
    · unfold projectStore
      rw [h_parent_b_some]
      simp
      exact h_inner_b_ne
    · unfold projectStore
      rw [h_parent_a_some, h_parent_b_some]
      simp
      exact h_inner_eq

/-- Iterated single-variable `substFvar`: fold a list of `(y, y')` rename pairs
over an expression, applying the head first (matches `Block.applyRenames`'s fold
order on each expression position). -/
@[expose] def substFvarMany {P : PureExpr} [HasSubstFvar P] [HasFvar P]
    (e : P.Expr) (subst : List (P.Ident × P.Ident)) : P.Expr :=
  subst.foldl (fun acc p => HasSubstFvar.substFvar acc p.1 (HasFvar.mkFvar p.2)) e

@[simp] theorem substFvarMany_nil {P : PureExpr} [HasSubstFvar P] [HasFvar P]
    (e : P.Expr) : substFvarMany e ([] : List (P.Ident × P.Ident)) = e := rfl

@[simp] theorem substFvarMany_cons {P : PureExpr} [HasSubstFvar P] [HasFvar P]
    (e : P.Expr) (y y' : P.Ident) (rest : List (P.Ident × P.Ident)) :
    substFvarMany e ((y, y') :: rest)
      = substFvarMany (HasSubstFvar.substFvar e y (HasFvar.mkFvar y')) rest := rfl

/-- Resolve a variable through the rename list: `a ↦ b` for the FIRST `(a,b) ∈
subst`, else `x ↦ x`. -/
@[expose] def renameLookup {P : PureExpr} [DecidableEq P.Ident]
    (subst : List (P.Ident × P.Ident)) (x : P.Ident) : P.Ident :=
  match subst with
  | [] => x
  | (a, b) :: rest => if x = a then b else renameLookup rest x

@[simp] theorem renameLookup_nil {P : PureExpr} [DecidableEq P.Ident] (x : P.Ident) :
    renameLookup ([] : List (P.Ident × P.Ident)) x = x := rfl

@[simp] theorem renameLookup_cons {P : PureExpr} [DecidableEq P.Ident]
    (a b x : P.Ident) (rest : List (P.Ident × P.Ident)) :
    renameLookup ((a, b) :: rest) x = if x = a then b else renameLookup rest x := rfl

theorem renameLookup_notin {P : PureExpr} [DecidableEq P.Ident]
    (subst : List (P.Ident × P.Ident)) (x : P.Ident)
    (h : x ∉ subst.map Prod.fst) : renameLookup subst x = x := by
  induction subst with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨a, b⟩
    simp only [renameLookup_cons]
    have hxa : x ≠ a := by intro heq; subst heq; exact h (by simp)
    rw [if_neg hxa]
    exact ih (fun hmem => h (by simp [hmem]))

/-- When the rename's sources are distinct and `(a, b) ∈ subst`, `renameLookup`
resolves `a` to its (unique) target `b`. -/
theorem renameLookup_mem {P : PureExpr} [DecidableEq P.Ident]
    (subst : List (P.Ident × P.Ident))
    (h_src_nodup : (subst.map Prod.fst).Nodup)
    {a b : P.Ident} (h_pair : (a, b) ∈ subst) : renameLookup subst a = b := by
  induction subst with
  | nil => simp at h_pair
  | cons hd tl ih =>
    rcases hd with ⟨a', b'⟩
    rcases List.mem_cons.mp h_pair with h_eq | h_in
    · cases h_eq; simp
    · have ha_a' : a ≠ a' := by
        intro heq; subst heq
        simp only [List.map_cons, List.nodup_cons] at h_src_nodup
        exact h_src_nodup.1 (List.mem_map.mpr ⟨(a, b), h_in, rfl⟩)
      simp only [renameLookup_cons, if_neg ha_a']
      exact ih (by simp only [List.map_cons, List.nodup_cons] at h_src_nodup; exact h_src_nodup.2) h_in

/-- The iterated-substitution half: evaluating the renamed expression in `σ_h`
equals evaluating the ORIGINAL expression in the "renamed-lookup" store
`fun x => σ_h (renameLookup subst x)`.  Proved by HEAD-peel induction on `subst`,
discharging each head pair by single-pair `WellFormedSemanticEvalSubstFvar`. -/
theorem substFvarMany_eval_tweak {P : PureExpr}
    [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (δ : SemanticEval P)
    {e : P.Expr} {σ_h : SemanticStore P}
    (subst : List (P.Ident × P.Ident))
    (h_src_nodup : (subst.map Prod.fst).Nodup)
    (h_disjoint : ∀ a ∈ subst.map Prod.fst, a ∉ subst.map Prod.snd)
    (h_tgt_nodup : (subst.map Prod.snd).Nodup)
    (h_wfsubst : WellFormedSemanticEvalSubstFvar δ) :
    δ (fun x => σ_h (renameLookup subst x)) e = δ σ_h (substFvarMany e subst) := by
  classical
  induction subst generalizing e with
  | nil => simp
  | cons hd tl ih =>
    rcases hd with ⟨y, y'⟩
    have h_y'_notin_tl_fst : y' ∉ tl.map Prod.fst := by
      intro hmem
      have h_y'_tgt : y' ∈ (((y, y') :: tl).map Prod.snd) := by simp
      exact h_disjoint y' (by simp [hmem]) h_y'_tgt
    have h_step :
        δ (fun x => σ_h (renameLookup ((y, y') :: tl) x)) e
          = δ (fun x => σ_h (renameLookup tl x))
              (HasSubstFvar.substFvar e y (HasFvar.mkFvar y')) := by
      apply h_wfsubst e y y'
      · intro x hxy; simp only [renameLookup_cons, if_neg hxy]
      · rw [renameLookup_notin tl y' h_y'_notin_tl_fst]
        simp only [renameLookup_cons, if_true]
    rw [h_step, substFvarMany_cons]
    apply ih
    · have := h_src_nodup; simp only [List.map_cons, List.nodup_cons] at this; exact this.2
    · intro a ha hb; exact h_disjoint a (by simp [ha]) (by simp [hb])
    · have := h_tgt_nodup; simp only [List.map_cons, List.nodup_cons] at this; exact this.2

/-- Add new VACUOUS subst pairs (and widen `B`), extending the hoist store at the
new targets with arbitrary values.  This is the store-side core of the
prelude-havoc step: after the fresh prelude `init y'` havocs run, the augmented
`HoistInv A (B ++ B_new) (subst ++ subst_new)` holds between the (unchanged)
source store and the extended hoist store.

The new pairs `subst_new` have all SOURCE keys undefined in `σ_src`
(`h_new_src_undef`) — component (2) is vacuous for them.  `σ_h'` differs from
`σ_h` only on `B_new` (`h_extend`).  Existing pairs keep their value because their
targets `b ∈ B` (`h_subst_tgt_in_B`) and `B` is disjoint from `B_new`
(`h_B_disjoint`).  The frame widens because `A ∪ (B ++ B_new) ⊇ A ∪ B`. -/
theorem HoistInv.add_vacuous_pairs {P : PureExpr} [DecidableEq P.Ident]
    {A B B_new : List P.Ident}
    {subst subst_new : List (P.Ident × P.Ident)}
    {σ_src σ_h σ_h' : SemanticStore P}
    (h_new_src_undef : ∀ a ∈ subst_new.map Prod.fst, σ_src a = none)
    (h_subst_tgt_in_B : ∀ b ∈ subst.map Prod.snd, b ∈ B)
    (h_extend : ∀ x, x ∉ B_new → σ_h' x = σ_h x)
    (h_B_disjoint : ∀ b ∈ B, b ∉ B_new)
    (h : HoistInv (P := P) A B subst σ_src σ_h) :
    HoistInv (P := P) A (B ++ B_new) (subst ++ subst_new) σ_src σ_h' := by
  refine ⟨?_, ?_⟩
  · intro x h_x_notin_A h_x_notin_BB h_x_ne
    have h_x_notin_B : x ∉ B := fun hxB => h_x_notin_BB (List.mem_append.mpr (Or.inl hxB))
    have h_x_notin_Bnew : x ∉ B_new := fun hxBn => h_x_notin_BB (List.mem_append.mpr (Or.inr hxBn))
    rw [h_extend x h_x_notin_Bnew]
    exact h.1 x h_x_notin_A h_x_notin_B h_x_ne
  · intro a b h_pair h_src_ne
    rcases List.mem_append.mp h_pair with h_old | h_new
    · obtain ⟨h_b_ne, h_eq⟩ := h.2 a b h_old h_src_ne
      have h_b_in_B : b ∈ B := h_subst_tgt_in_B b (List.mem_map.mpr ⟨(a, b), h_old, rfl⟩)
      have h_b_notin_Bnew : b ∉ B_new := h_B_disjoint b h_b_in_B
      rw [h_extend b h_b_notin_Bnew]
      exact ⟨h_b_ne, h_eq⟩
    · exfalso
      apply h_src_ne
      exact h_new_src_undef a (List.mem_map.mpr ⟨(a, b), h_new, rfl⟩)

/-! ## Phase 8 Option F — Evaluator transport for HoistInv

Under the guarded frame, expression evaluation transports across `HoistInv` via
the multi-pair keystone `substFvarMany_eval_tweak`: a renamed expression
evaluates on the hoist store to the same value the source expression evaluates
to, because each read variable is either frame-agreed or paired by the subst. -/

/-! ### Single-pair substFvar congruence-bridge (reusable)

`Block.applyRenames` for the fresh-name `.loop` arm rewrites every expression
position (renamed init RHS, the loop guard, assert/assume/cover conditions, and
all recursively nested body subexpressions) by a SINGLE rename pair `(y, y')` —
the per-iteration body simulation transports each such expression one rename at
a time.  The transport principle for one pair is:

  `δ σ_src e = δ σ_h (substFvar e y (mkFvar y'))`

under the `HoistInv`-style pairing facts at `(y, y')`.

The subtlety (the reason this needs its own lemma rather than a direct appeal to
`WellFormedSemanticEvalSubstFvar`) is that `WellFormedSemanticEvalSubstFvar`'s
frame premise is `∀ x ≠ y, σ x = σ' x`, which **fails at `x = y'`**: the source
store `σ_src` and hoist store `σ_h` need not agree at the fresh target `y'`
(indeed `σ_src y' = none` body-locally while `σ_h y' = some _`).  We therefore
compose `WellFormedSemanticEvalSubstFvar` with `WellFormedSemanticEvalExprCongr`
through a tweak store

  `σ_t x := if x = y then σ_h y' else σ_h x`

so that (1) `σ_t` agrees with `σ_src` on `getVars e` (congruence swaps
`σ_src ⇝ σ_t`), and (2) `σ_t` agrees with `σ_h` away from `y` and carries
`σ_t y = σ_h y'` (substFvar applies with `σ := σ_t`, `σ' := σ_h`).

This is the single-pair counterpart of the multi-pair keystone
`substFvarMany_eval_tweak`; it is exposed separately so the per-iteration body
simulation can call it uniformly on each rewritten expression position without
threading the rename-list well-formedness side conditions. -/

/-- A successful evaluation `δ σ e = some v` (under `WellFormedSemanticEvalDef`)
defines every read var of `e`: `σ x ≠ none` for `x ∈ getVars e`.  This is the
read-var-definedness discharge the guarded-frame expression transports consume. -/
theorem read_vars_def_of_eval {P : PureExpr} [HasVarsPure P P.Expr]
    {δ : SemanticEval P} {σ : SemanticStore P} {e : P.Expr} {v : P.Expr}
    (h_wfdef : WellFormedSemanticEvalDef δ)
    (h_eval : δ σ e = some v) :
    ∀ x ∈ HasVarsPure.getVars e, σ x ≠ none := by
  intro x hx h_none
  have h_some : (σ x).isSome = true := h_wfdef e v σ h_eval x hx
  rw [h_none] at h_some; simp at h_some

/-- Split `.stmts (s :: rest) ρ ⟶* .terminal ρ'` into head and tail runs. -/
private theorem stmts_cons_terminal_inv
    [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr]
    {extendEval : ExtendEval P}
    {s : Stmt P (Cmd P)} {rest : List (Stmt P (Cmd P))} {ρ ρ' : Env P}
    (h : StepStmtStar P (EvalCmd P) extendEval (.stmts (s :: rest) ρ) (.terminal ρ')) :
    ∃ ρ_mid : Env P,
      StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ) (.terminal ρ_mid) ∧
      StepStmtStar P (EvalCmd P) extendEval (.stmts rest ρ_mid) (.terminal ρ') := by
  cases h with
  | step _ _ _ h1 hr1 => cases h1; exact seq_reaches_terminal P (EvalCmd P) extendEval hr1

/-! ## `extendStoreMany`: store extended by a list of bindings

Extend a store with a list of `(ident, value)` bindings, applied front-to-back
via `List.foldl` — matching the order in which a hoisted prelude
`[init y₀ ; init y₁ ; ...]` populates the entry store. Consumed by the loop
driver's prelude bridge. -/

/-- Extend a `SemanticStore` with a list of `(ident, value)` bindings,
applying the head binding first.  Front of the list ends up "innermost". -/
@[expose] def extendStoreMany {P : PureExpr} [DecidableEq P.Ident]
    (σ : SemanticStore P) (bindings : List (P.Ident × P.Expr)) :
    SemanticStore P :=
  bindings.foldl (fun σ p =>
    StructuredToUnstructuredCorrect.extendStoreOne σ p.1 p.2) σ

@[simp] theorem extendStoreMany_nil {P : PureExpr} [DecidableEq P.Ident]
    (σ : SemanticStore P) :
    extendStoreMany σ [] = σ := rfl

@[simp] theorem extendStoreMany_cons {P : PureExpr} [DecidableEq P.Ident]
    (σ : SemanticStore P) (y : P.Ident) (v : P.Expr)
    (rest : List (P.Ident × P.Expr)) :
    extendStoreMany σ ((y, v) :: rest)
      = extendStoreMany
          (StructuredToUnstructuredCorrect.extendStoreOne σ y v) rest := rfl

end Imperative