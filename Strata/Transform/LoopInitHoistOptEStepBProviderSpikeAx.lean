/-
Axiom audit for the Step B provider.  `#print axioms` cannot run under a
`module` header, so this non-module file imports the provider and prints the
axiom dependencies of its load-bearing lemmas.  A clean result is
`[propext, Classical.choice, Quot.sound]` with NO `sorryAx`.
-/
import Strata.Transform.LoopInitHoistOptEStepBProviderSpike

-- The cons-sequencer (generic structural glue).
#print axioms Imperative.OptEStepBProvider.bodySimE_cons
#print axioms Imperative.OptEStepBProvider.bodySimE_nil
#print axioms Imperative.OptEStepBProvider.bodySimE_to_bodySim
-- The CRITICAL new self-referential composition: nested-loop StmtSimE via the
-- recursive renamed-guard driver call.
#print axioms Imperative.OptEStepBProvider.nestedLoop_stmtSimE
-- The concrete body₃ reduction (rename descends into nested loop).
#print axioms Imperative.OptEStepBProvider.body₃_concrete
-- The assembled OUTER body_sim for the init :: [nested loop] body.
#print axioms Imperative.OptEStepBProvider.outer_bodySim_concrete
-- The full end-to-end OUTER loop simulation.
#print axioms Imperative.OptEStepBProvider.outer_loop_simulation_concrete
