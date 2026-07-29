/-! # Verification conditions (Tier 3: multi-target, imperative-vs-spec)

NTP4VC-inspired VCs (github.com/xqyww123/NTP4VC): `fact_vcg` (FactImperative vs
FactRecursive) and `gcd_vcg` (EuclideanAlgorithm), ported to core Lean 4.

This file deliberately holds MULTIPLE `sorry` targets, one of which is only
provable by first establishing a stronger helper (the accumulator generalization
`factLoop_eq`). It exercises the multi-theorem / transitive-sorry machinery
(the file-root over N targets + the `#print axioms` gate that flags a theorem as
unproven when it transitively depends on a helper that still has `sorry`). -/

-- fact_vcg: the recursive factorial spec.
def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fact n

-- The imperative (tail-recursive, accumulator) factorial.
def factLoop (n acc : Nat) : Nat :=
  match n with
  | 0 => acc
  | k+1 => factLoop k ((k+1) * acc)

-- fact_vcg (fact_impqtvc): the imperative loop matches the recursive spec.
-- The natural proof route generalizes over the accumulator first.
theorem factLoop_eq (n acc : Nat) : factLoop n acc = fact n * acc := by
  sorry

-- The correctness VC itself — closed from `factLoop_eq` at `acc = 1`.
theorem factLoop_correct (n : Nat) : factLoop n 1 = fact n := by
  sorry

-- gcd_vcg (euclidqtvc): the Euclid recursion step preserves the gcd.
theorem gcd_rec_vc (a b : Nat) (h : 0 < b) : Nat.gcd a b = Nat.gcd b (a % b) := by
  sorry
