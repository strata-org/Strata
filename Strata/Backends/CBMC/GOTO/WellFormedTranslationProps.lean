/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOInvariants
public import Strata.Backends.CBMC.GOTO.SemanticsTautschnig

public section

/-! # Consequences of `WellFormedTranslation`

Bridge lemmas linking `WellFormedTranslation`'s structural fields to
the per-step bridge obligations consumed by
`SteppingBridgesDischarge`.

Currently:

* `findLocIdx_resolves` — under `locationNum_eq_index`, tautschnig's
  `findLocIdx` resolves a `locationNum` back to its index. Used by
  `Bisim.stepGoto_goto_taken_to_stepInstr` and the bridge's
  `goto_target_resolves` field. -/

namespace CProverGOTO

/-- Helper: `findLocIdx.go i list k = some i` whenever:

* every list element's `locationNum` is `k + its-list-position`,
* `k ≤ i`,
* `i < k + list.length` (so `i - k` is a valid index into `list`).

The recursion is on the list. -/
private theorem findLocIdx_go_resolves
    (i : Nat) :
    ∀ (l : List Instruction) (k : Nat),
      k ≤ i →
      i < k + l.length →
      (∀ j, ∀ instr_j, l[j]? = some instr_j → instr_j.locationNum = k + j) →
      SemanticsTautschnig.findLocIdx.go i l k = some i
  | [], k, _, h_lt, _ => by
    simp at h_lt
    omega
  | head :: tail, k, h_k_le, h_lt, h_loc => by
    -- Case-split on k = i vs k < i.
    by_cases h_eq : k = i
    · -- k = i: the head must have locationNum = i.
      subst h_eq
      have h_head_loc : head.locationNum = k := by
        have : (head :: tail)[0]? = some head := rfl
        have := h_loc 0 head this
        simp at this; exact this
      simp only [SemanticsTautschnig.findLocIdx.go, h_head_loc,
                 beq_self_eq_true, ite_true]
    · -- k < i: head.locationNum = k ≠ i.
      have h_k_lt : k < i := by omega
      have h_head_loc : head.locationNum = k := by
        have h_at : (head :: tail)[0]? = some head := rfl
        have := h_loc 0 head h_at
        simp at this; exact this
      have h_neq : (head.locationNum == i) = false := by
        simp [h_head_loc]; omega
      simp only [SemanticsTautschnig.findLocIdx.go, h_neq]
      apply findLocIdx_go_resolves i tail (k + 1)
      · omega
      · simp at h_lt; omega
      · intro j instr_j h_at_j
        have h_at_cons : (head :: tail)[j + 1]? = some instr_j := h_at_j
        have := h_loc (j + 1) instr_j h_at_cons
        omega

/-- Under `locationNum_eq_index`, walking `findLocIdx` from index 0
locates the instruction with `locationNum = i` at array index `i`.

Concretely: if `pgm.instrAt i = some instr` and every instruction's
`locationNum` equals its array index, then
`findLocIdx pgm.instructions i = some i`. -/
theorem findLocIdx_resolves
    {pgm : Program} (i : Nat) (instr : Instruction)
    (h_locNum_eq_idx :
      ∀ j, ∀ instr', pgm.instrAt j = some instr' → instr'.locationNum = j)
    (h_at : pgm.instrAt i = some instr) :
    SemanticsTautschnig.findLocIdx pgm.instructions i = some i := by
  unfold SemanticsTautschnig.findLocIdx
  have h_i_lt_size : i < pgm.instructions.size := by
    unfold Program.instrAt at h_at
    rcases Nat.lt_or_ge i pgm.instructions.size with h_lt | h_ge
    · exact h_lt
    · rw [Array.getElem?_eq_none h_ge] at h_at; cases h_at
  apply findLocIdx_go_resolves i pgm.instructions.toList 0
  · omega
  · simp only [Array.length_toList, Nat.zero_add]; exact h_i_lt_size
  · intro j instr_j h_at_j
    have h_at_array : pgm.instructions[j]? = some instr_j := by
      rw [Array.getElem?_toList] at h_at_j; exact h_at_j
    have h_at_pgm : pgm.instrAt j = some instr_j := h_at_array
    have h_loc := h_locNum_eq_idx j instr_j h_at_pgm
    rw [h_loc, Nat.zero_add]

end CProverGOTO
