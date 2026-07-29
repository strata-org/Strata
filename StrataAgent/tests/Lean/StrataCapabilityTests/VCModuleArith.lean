module

/-! # Module-system warm-up (Tier 1: proven-in-a-module)

A `module` file with a single `public` theorem. This is the SIMPLEST end-to-end
trigger of the module axiom-oracle path: the target is copied verbatim into
Sandbox/Stub.lean (which keeps the `module` header), so once the agent discharges
the `sorry`, success can ONLY be confirmed by the out-of-module `#print axioms`
probe — in-module `#print axioms` is a hard Lean error. The old oracle could
never confirm a proof here; this file regression-guards that it now can.

`public` is required so the out-of-module scratch file can see the decl. -/

public theorem module_add_comm_vc (a b : Nat) : a + b = b + a := by
  sorry
