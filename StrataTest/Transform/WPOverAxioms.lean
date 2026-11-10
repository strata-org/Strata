/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.WP.WPCoreCorrect

/-!
## Axioms of the WP over-approximation theorems

The over-approximation of the WP phase (`wp_runsOverapproximate`,
`wpLoopFree_runsOverapproximate`), the typing of its output (`wpEntry_wellTyped`) and the run of
its pipeline phase (`wpPipelinePhase_ok`) depend on the standard axioms only.
-/

/--
info: 'Core.WP.wp_runsOverapproximate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Core.WP.wp_runsOverapproximate

/--
info: 'Core.WP.wpLoopFree_runsOverapproximate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Core.WP.wpLoopFree_runsOverapproximate

/--
info: 'Core.WP.wpEntry_wellTyped' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Core.WP.wpEntry_wellTyped

/--
info: 'Core.WP.wpPipelinePhase_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Core.WP.wpPipelinePhase_ok
