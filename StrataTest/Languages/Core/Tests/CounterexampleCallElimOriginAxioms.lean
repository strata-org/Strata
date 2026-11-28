/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Counterexample.BackLinkCallElimOrigin

/-!
# callElim origin extractor: axiom check

The extractor `Core.CallElim.callElimOrigin'` and its per-call helper
`Core.CallElim.recordCallOrigin` depend only on `propext`, `Classical.choice` and
`Quot.sound`: in particular not on `sorryAx` (a `sorry` or `admit`) nor on
`Lean.ofReduceBool` (a `native_decide`). The `#guard_msgs` docstrings pin the axiom
set. This file is not a `module`, because `#print axioms` cannot appear in a `module`
file; `CounterexampleCallElimOriginTest.lean` holds the behavioural tests.
-/

open Core Core.CallElim

/--
info: 'Core.CallElim.callElimOrigin'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Core.CallElim.callElimOrigin'

/--
info: 'Core.CallElim.recordCallOrigin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Core.CallElim.recordCallOrigin
