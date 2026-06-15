/- Axiom checker for the `.loop`-arm driver library.  `#print axioms` cannot run
   under a `module` header, so this non-module file imports the driver and prints
   the axiom dependencies of its load-bearing lemmas.  A clean result is
   `[propext, Classical.choice, Quot.sound]` with NO `sorryAx`. -/
import Strata.Transform.LoopInitHoistLoopDriver

#print axioms Imperative.LoopInitHoistLoopDriver.loopDet_lift_2g_fuel
#print axioms Imperative.LoopInitHoistLoopDriver.loopDet_lift_2g
#print axioms Imperative.LoopInitHoistLoopDriver.loopDet_lift_2g_recovers_single
#print axioms Imperative.LoopInitHoistLoopDriver.renamed_guard_eval_same_delta
#print axioms Imperative.LoopInitHoistLoopDriver.loopDet_lift_renamedGuard
#print axioms Imperative.LoopInitHoistLoopDriver.entries_from_lift
#print axioms Imperative.LoopInitHoistLoopDriver.prelude_run_list_md
#print axioms Imperative.LoopInitHoistLoopDriver.prelude_bridge_list_md
#print axioms Imperative.LoopInitHoistLoopDriver.bridge_out_nested_union
#print axioms Imperative.LoopInitHoistLoopDriver.bridge_out_union_list
#print axioms Imperative.LoopInitHoistLoopDriver.bound_Bo_through_stepB
#print axioms Imperative.LoopInitHoistLoopDriver.compose_union
#print axioms Imperative.LoopInitHoistLoopDriver.bodySim_is_driver_slot
