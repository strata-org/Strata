/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-!
# Sequence Axiom Model

Lean theorems over `List` that are isomorphic to the sequence axioms declared
in `Factory.lean`.  Each theorem is named after the axiom it models and carries
a doc-comment referencing the corresponding Factory function.

## Mapping

| Strata Sequence op        | Lean List op                        |
|---------------------------|-------------------------------------|
| `Sequence a`              | `List α`                            |
| `Sequence.length(s)`      | `s.length`                          |
| `Sequence.select(s, i)`   | `s[i]`                              |
| `Sequence.empty`          | `[]`                                |
| `Sequence.append(s0, s1)` | `s0 ++ s1`                          |
| `Sequence.build(s, v)`    | `s ++ [v]`  (snoc)                  |
| `Sequence.update(s, i, v)`| `s.set i v`                         |
| `Sequence.contains(s, v)` | `v ∈ s`                             |
| `Sequence.take(s, n)`     | `s.take n`                          |
| `Sequence.drop(s, n)`     | `s.drop n`                          |

All index variables are `Nat` (the natural model of the non-negative `Int`
indices used in the SMT axioms).
-/

namespace Strata.SeqModel

-- ════════════════════════════════════════════════════════════════
-- seqLengthFunc axiom: length(s) >= 0
-- ════════════════════════════════════════════════════════════════

/-- `seqLengthFunc`: `length(s) >= 0`.  Trivially true for `Nat`. -/
theorem length_nonneg (s : List α) : 0 ≤ s.length :=
  Nat.zero_le _

-- ════════════════════════════════════════════════════════════════
-- seqEmptyFunc axiom: length(empty()) == 0
-- ════════════════════════════════════════════════════════════════

/-- `seqEmptyFunc`: `length(empty()) == 0`. -/
theorem length_empty : ([] : List α).length = 0 :=
  rfl

-- ════════════════════════════════════════════════════════════════
-- seqAppendFunc axioms
-- ════════════════════════════════════════════════════════════════

/-- `seqAppendFunc` axiom 1:
    `length(append(s0, s1)) == length(s0) + length(s1)`. -/
theorem append_length (s0 s1 : List α) :
    (s0 ++ s1).length = s0.length + s1.length :=
  @List.length_append _ s0 s1

/-- `seqAppendFunc` axiom 2:
    `0 <= n < length(s0) ==> select(append(s0, s1), n) == select(s0, n)`. -/
theorem append_select_left (s0 s1 : List α) (n : Nat)
    (hn : n < s0.length) {h : n < (s0 ++ s1).length} :
    (s0 ++ s1)[n] = s0[n] :=
  List.getElem_append_left hn

/-- `seqAppendFunc` axiom 3:
    `n >= length(s0) ∧ n < length(s0) + length(s1)
     ==> select(append(s0, s1), n) == select(s1, n - length(s0))`. -/
theorem append_select_right (s0 s1 : List α) (n : Nat)
    (hge : s0.length ≤ n) {h : n < (s0 ++ s1).length} :
    (s0 ++ s1)[n] = s1[n - s0.length]'(by simp at h; omega) :=
  List.getElem_append_right hge

-- ════════════════════════════════════════════════════════════════
-- seqBuildFunc axioms  (build = snoc = s ++ [v])
-- ════════════════════════════════════════════════════════════════

/-- `seqBuildFunc` axiom 1:
    `length(build(s, v)) == 1 + length(s)`. -/
theorem build_length (s : List α) (v : α) :
    (s ++ [v]).length = s.length + 1 := by
  simp

/-- `seqBuildFunc` axiom 2:
    `i == length(s) ==> select(build(s, v), i) == v`. -/
theorem build_select_last (s : List α) (v : α)
    {h : s.length < (s ++ [v]).length} :
    (s ++ [v])[s.length] = v := by
  simp

/-- `seqBuildFunc` axiom 3:
    `0 <= i < length(s) ==> select(build(s, v), i) == select(s, i)`. -/
theorem build_select_old (s : List α) (v : α) (i : Nat)
    (hi : i < s.length) {h : i < (s ++ [v]).length} :
    (s ++ [v])[i] = s[i] :=
  List.getElem_append_left hi

-- ════════════════════════════════════════════════════════════════
-- seqUpdateFunc axioms  (update = List.set)
-- ════════════════════════════════════════════════════════════════

/-- `seqUpdateFunc` axiom 1:
    `length(update(s, i, v)) == length(s)`. -/
theorem update_length (s : List α) (i : Nat) (v : α) :
    (s.set i v).length = s.length :=
  List.length_set

/-- `seqUpdateFunc` axiom 2:
    `0 <= i < length(s) ==> select(update(s, i, v), i) == v`. -/
theorem update_select_same (s : List α) (i : Nat) (v : α)
    (_hi : i < s.length) {h : i < (s.set i v).length} :
    (s.set i v)[i] = v := by
  simp

/-- `seqUpdateFunc` axiom 3:
    `0 <= n < length(s) ∧ n ≠ i
     ==> select(update(s, i, v), n) == select(s, n)`. -/
theorem update_select_other (s : List α) (i n : Nat) (v : α)
    (hn : n < s.length) (hne : i ≠ n)
    {h : n < (s.set i v).length} :
    (s.set i v)[n] = s[n] :=
  List.getElem_set_ne hne h

-- ════════════════════════════════════════════════════════════════
-- seqContainsFunc axiom
-- ════════════════════════════════════════════════════════════════

/-- `seqContainsFunc`:
    `contains(s, v) ↔ ∃ i, 0 <= i < length(s) ∧ select(s, i) == v`. -/
theorem contains_iff_exists (s : List α) (v : α) :
    v ∈ s ↔ ∃ i, ∃ h : i < s.length, s[i] = v :=
  List.mem_iff_getElem

-- ════════════════════════════════════════════════════════════════
-- seqTakeFunc axioms
-- ════════════════════════════════════════════════════════════════

/-- `seqTakeFunc` axiom 1:
    `0 <= n <= length(s) ==> length(take(s, n)) == n`. -/
theorem take_length (s : List α) (n : Nat) (hn : n ≤ s.length) :
    (s.take n).length = n := by
  simp [Nat.min_eq_left hn]

/-- `seqTakeFunc` axiom 2:
    `0 <= j < n ==> select(take(s, n), j) == select(s, j)`. -/
theorem take_select (s : List α) (n j : Nat)
    (_hj : j < n) {h₁ : j < (s.take n).length} {h₂ : j < s.length} :
    (s.take n)[j] = s[j] :=
  List.getElem_take

-- ════════════════════════════════════════════════════════════════
-- seqDropFunc axioms
-- ════════════════════════════════════════════════════════════════

/-- `seqDropFunc` axiom 1:
    `0 <= n <= length(s) ==> length(drop(s, n)) == length(s) - n`.
    In Lean this holds unconditionally. -/
theorem drop_length (s : List α) (n : Nat) :
    (s.drop n).length = s.length - n :=
  List.length_drop

/-- `seqDropFunc` axiom 2:
    `0 <= j < length(s) - n ==> select(drop(s, n), j) == select(s, j + n)`. -/
theorem drop_select (s : List α) (n j : Nat)
    {h₁ : j < (s.drop n).length} (hjn : j + n < s.length) :
    (s.drop n)[j] = s[j + n] := by
  simp [List.getElem_drop, Nat.add_comm]

end Strata.SeqModel
