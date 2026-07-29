/-! # Verification-condition warm-ups (Tier 2: list/array VCs by induction)

NTP4VC-inspired VCs (github.com/xqyww123/NTP4VC), ported to core Lean 4 (no
Mathlib). These mirror the array/sequence proof obligations from benchmarks like
`add_list_vcg`, `coincidence_count_list_vcg`, and `insertion_sort_list_vcg` —
facts about folding/length over sequences that require an induction on the list.

Harder than Tier 1: `omega` alone won't close them; the prover must set up a
structural induction. -/

-- add_list_vcg-style summation spec.
def sumList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumList xs

-- Summing a concatenation is the sum of the parts (loop-split VC).
theorem sum_append_vc (xs ys : List Nat) :
    sumList (xs ++ ys) = sumList xs + sumList ys := by
  sorry

-- length of a concatenation (array-bounds VC).
theorem length_append_vc (xs ys : List Nat) :
    (xs ++ ys).length = xs.length + ys.length := by
  sorry

-- inverse_in_place_vcg-style: reversing preserves length.
theorem reverse_length_vc (xs : List Nat) : xs.reverse.length = xs.length := by
  sorry
