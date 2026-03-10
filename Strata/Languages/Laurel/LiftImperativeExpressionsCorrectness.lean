/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.LiftImperativeExpressions
import Strata.Languages.Laurel.LaurelSemantics
import Strata.Languages.Laurel.LaurelSemanticsProps

/-!
# Correctness of LiftImperativeExpressions — Phase 2: Single Assignment

Phase 2 of the bottom-up correctness proof for the lifting pass.
See `docs/designs/design-correctness-theorem-for-liftimperativeexpre.md`.

## Concrete Case

Expression: `op(x, x := e)` where `e` is pure (evaluates identically in
any store that extends the original with fresh variables).

After lifting:
```
  var snap := x;     -- snapshot x before assignment
  x := e;            -- the assignment
  op(snap, x)        -- cleaned expression using snapshot
```

## Main Results

- `lift_single_assign_correct`: constructive form — given the semantic
  components, construct a derivation for the lifted block.
- `lift_single_assign_from_eval`: derivation-based form — decompose an
  original `prim_op` derivation and apply the constructive form.

## Design Reference

Option C (Phased bottom-up proof), Phase 2: single assignment in PrimitiveOp.
-/

namespace Strata.Laurel

/-! ## BEq/Ne helper for String (Identifier) -/

private theorem beq_false_of_ne {a b : String} (h : a ≠ b) : (a == b) = false := by
  simp [h]

/-! ## Constructive form -/

/-- Given the semantic components of evaluating `op(x, x := e)`, construct
a derivation showing the lifted block `[var snap := x; x := e; op(snap, x)]`
produces the same result.

This is the core Phase 2 theorem. The hypotheses directly state what the
original evaluation computes, avoiding the need to invert mutual inductives. -/
theorem lift_single_assign_correct
    (δ : LaurelEval) (π : ProcEnv) (h : LaurelHeap) (σ : LaurelStore)
    (op : Operation) (x snap : Identifier)
    (e : StmtExprMd) (ty : HighTypeMd)
    (md tmd : Imperative.MetaData Core.Expression)
    (v_old v_new result : LaurelValue)
    (hx_def : σ x = some v_old)
    (hfresh : σ snap = none)
    (hne : snap ≠ x)
    (he_ext : ∀ σ', (∀ y, y ≠ snap → σ' y = σ y) →
      EvalLaurelStmt δ π h σ' e h σ' (.normal v_new))
    (hop : evalPrimOp op [v_old, v_new] = some result) :
    ∃ σ_block, EvalLaurelBlock δ π h σ
      [ ⟨.LocalVariable snap ty (some ⟨.Identifier x, md⟩), md⟩,
        ⟨.Assign [⟨.Identifier x, tmd⟩] e, md⟩,
        ⟨.PrimitiveOp op [⟨.Identifier snap, md⟩, ⟨.Identifier x, md⟩], md⟩ ]
      h σ_block (.normal result) := by
  -- Define intermediate stores
  let σ_snap : LaurelStore := fun y => if y == snap then some v_old else σ y
  let σ_final : LaurelStore := fun y => if y == x then some v_new else σ_snap y
  -- Key store facts
  have h_snap_self : σ_snap snap = some v_old := by simp [σ_snap]
  have h_snap_x : σ_snap x = some v_old := by
    simp only [σ_snap]; simp [beq_iff_eq, Ne.symm hne, hx_def]
  have h_final_snap : σ_final snap = some v_old := by
    simp only [σ_final]; simp [beq_iff_eq, hne, h_snap_self]
  have h_final_x : σ_final x = some v_new := by simp [σ_final]
  -- e evaluates to v_new in σ_snap (by purity / store-extension invariance)
  have he_snap : EvalLaurelStmt δ π h σ_snap e h σ_snap (.normal v_new) := by
    apply he_ext; intro y hne'
    simp only [σ_snap]; simp [beq_iff_eq, hne']
  -- InitStore for snap
  have h_init : InitStore σ snap v_old σ_snap :=
    .init hfresh h_snap_self (fun y hne' => by
      simp only [σ_snap]; simp [beq_iff_eq, Ne.symm hne'])
  -- UpdateStore for x := v_new in σ_snap
  have h_upd : UpdateStore σ_snap x v_new σ_final :=
    .update (v' := v_old) h_snap_x h_final_x (fun y hne' => by
      simp only [σ_final]; simp [beq_iff_eq, Ne.symm hne'])
  -- Assemble the block: [LocalVariable, Assign, PrimitiveOp]
  exact ⟨σ_final, .cons_normal
    (.local_var_init (.identifier hx_def) hfresh h_init)
    (by simp)
    (.cons_normal
      (.assign_single he_snap h_snap_x h_upd)
      (by simp)
      (.last_normal
        (.prim_op
          (.cons (.identifier h_final_snap) (.cons (.identifier h_final_x) .nil))
          hop)))⟩

-- ## Derivation-based form

set_option maxHeartbeats 800000 in
/-- Given a derivation of `op(x, x := e)`, produce a derivation of the
lifted block. Requires that `e` is pure: it evaluates to `v_new` without
changing heap or store, and evaluates identically in any store that agrees
with the original store on all variables except `snap`. -/
theorem lift_single_assign_from_eval
    (δ : LaurelEval) (π : ProcEnv) (h : LaurelHeap) (σ : LaurelStore)
    (op : Operation) (x snap : Identifier)
    (e : StmtExprMd) (ty : HighTypeMd)
    (md tmd : Imperative.MetaData Core.Expression)
    (h' : LaurelHeap) (σ' : LaurelStore) (result : LaurelValue)
    (v_new : LaurelValue)
    (heval : EvalLaurelStmt δ π h σ
      ⟨.PrimitiveOp op [⟨.Identifier x, md⟩,
                         ⟨.Assign [⟨.Identifier x, tmd⟩] e, md⟩], md⟩
      h' σ' (.normal result))
    (hfresh : σ snap = none)
    (hne : snap ≠ x)
    (he_pure : EvalLaurelStmt δ π h σ e h σ (.normal v_new))
    (he_ext : ∀ σ₀, (∀ y, y ≠ snap → σ₀ y = σ y) →
      EvalLaurelStmt δ π h σ₀ e h σ₀ (.normal v_new)) :
    ∃ σ_block, EvalLaurelBlock δ π h σ
      [ ⟨.LocalVariable snap ty (some ⟨.Identifier x, md⟩), md⟩,
        ⟨.Assign [⟨.Identifier x, tmd⟩] e, md⟩,
        ⟨.PrimitiveOp op [⟨.Identifier snap, md⟩, ⟨.Identifier x, md⟩], md⟩ ]
      h' σ_block (.normal result) := by
  -- Invert the original derivation
  cases heval with
  | prim_op hargs hop_eq =>
    cases hargs with
    | cons harg1 hrest =>
      cases hrest with
      | cons harg2 hnil =>
        cases hnil
        cases harg1 with
        | identifier hlookup =>
          cases harg2 with
          | assign_single heval_e _hexists hupdate =>
            -- By determinism: heval_e agrees with he_pure on output state
            have ⟨hh_eq, hσ_eq, hv_eq⟩ := EvalLaurelStmt_deterministic heval_e he_pure
            -- hh_eq: output heap of e = h, hσ_eq: output store of e = σ
            -- Rewrite in hupdate and hop_eq rather than subst (to preserve names)
            cases hv_eq  -- unify the value
            rw [hh_eq] at *; rw [hσ_eq] at *
            exact lift_single_assign_correct δ π _ _ op x snap e ty md tmd
              _ _ result hlookup hfresh hne he_ext hop_eq

end Strata.Laurel
