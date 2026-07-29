module

/-! # Module-system multi-target (Tier 3: transitive-sorry gate in a module)

A `module` file with MULTIPLE `public` targets where the main VC is naturally
proven only via the helper. It exercises the module multi-theorem / transitive-
sorry machinery end-to-end: the axiom gate must report `factLoopM_correct` as
UNPROVEN while `factLoopM_eq` still has `sorry` (its axiom set transitively
contains `sorryAx` through the dependency), and flip to proven only once BOTH are
closed. Because it is a `module`, this can only be adjudicated by the out-of-
module `#print axioms` probe on the built olean — never by in-module printing or
a text/grep scan. `public` exposes every decl to the probe. -/

public def factM : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factM n

public def factLoopM (n acc : Nat) : Nat :=
  match n with
  | 0 => acc
  | k+1 => factLoopM k ((k+1) * acc)

-- Accumulator generalization (the helper the main VC needs).
public theorem factLoopM_eq (n acc : Nat) : factLoopM n acc = factM n * acc := by
  sorry

-- The correctness VC — closed from `factLoopM_eq` at `acc = 1`.
public theorem factLoopM_correct (n : Nat) : factLoopM n 1 = factM n := by
  sorry
