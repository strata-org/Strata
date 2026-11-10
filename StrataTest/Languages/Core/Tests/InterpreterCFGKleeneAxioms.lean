/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.InterpreterCFGProps
import Strata.Languages.Core.InterpreterKleeneProps

/-!
## Axioms of the CFG and Kleene interpreter theorems

The soundness and completeness theorems of the monadic CFG and Kleene drivers, generic and at
Core, depend on no axiom beyond `propext`, `Classical.choice` and `Quot.sound`.
-/

/-! ### Generic CFG driver -/

/--
info: 'Imperative.runInterpCFG_soundE' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Imperative.runInterpCFG_soundE

/--
info: 'Imperative.Calls.runInterpCFG_callSoundE'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Imperative.Calls.runInterpCFG_callSoundE

/--
info: 'Imperative.runInterpCFG_completeE' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Imperative.runInterpCFG_completeE

/--
info: 'Imperative.runInterpCFG_follows_fam' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Imperative.runInterpCFG_follows_fam

/--
info: 'Imperative.Calls.runInterpCFG_callCompleteE'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Imperative.Calls.runInterpCFG_callCompleteE

/--
info: 'Imperative.Calls.runInterpCFG_callComplete_follows'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Imperative.Calls.runInterpCFG_callComplete_follows

/--
info: 'Imperative.Calls.cfg_replayRun_complete'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Imperative.Calls.cfg_replayRun_complete

/-! ### Generic Kleene driver -/

/--
info: 'Imperative.runInterpKleene_soundE'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Imperative.runInterpKleene_soundE

/--
info: 'Imperative.Calls.runCallInterpKleene_soundE'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Imperative.Calls.runCallInterpKleene_soundE

/--
info: 'Imperative.Calls.runCallInterpKleene_replay_soundE'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Imperative.Calls.runCallInterpKleene_replay_soundE

/--
info: 'Imperative.runInterpKleene_completeE'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Imperative.runInterpKleene_completeE

/--
info: 'Imperative.runInterpKleene_engCompleteE'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Imperative.runInterpKleene_engCompleteE

/--
info: 'Imperative.runInterpKleene_follows_fam'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Imperative.runInterpKleene_follows_fam

/--
info: 'Imperative.Calls.runInterpKleene_callCompleteE'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Imperative.Calls.runInterpKleene_callCompleteE

/--
info: 'Imperative.Calls.runInterpKleene_callComplete_follows'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Imperative.Calls.runInterpKleene_callComplete_follows

/--
info: 'Imperative.Calls.kleene_replayRun_complete'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Imperative.Calls.kleene_replayRun_complete

/-! ### Choice resolution -/

/--
info: 'Imperative.not_chooseResolves_of_tt_ff' does not depend on any axioms
-/
#guard_msgs in
#print axioms Imperative.not_chooseResolves_of_tt_ff

/-! ### Core -/

/--
info: 'Core.runCoreInterpCFG_soundE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Core.runCoreInterpCFG_soundE

/--
info: 'Core.runCoreInterpCFG_soundE_of_evalFactoryWF'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.runCoreInterpCFG_soundE_of_evalFactoryWF

/--
info: 'Core.runCoreInterpCFG_completeE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Core.runCoreInterpCFG_completeE

/--
info: 'Core.runCoreInterpCFG_complete_follows'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.runCoreInterpCFG_complete_follows

/--
info: 'Core.runCoreInterpCFG_replayComplete'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.runCoreInterpCFG_replayComplete

/--
info: 'Core.runCoreInterpKleene_replay_soundE'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.runCoreInterpKleene_replay_soundE

/--
info: 'Core.runCoreInterpKleene_replay_soundE_of_evalFactoryWF'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.runCoreInterpKleene_replay_soundE_of_evalFactoryWF

/--
info: 'Core.runCoreInterpKleene_completeE'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.runCoreInterpKleene_completeE

/--
info: 'Core.runCoreInterpKleene_complete_follows'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.runCoreInterpKleene_complete_follows

/--
info: 'Core.runCoreInterpKleene_replayComplete'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.runCoreInterpKleene_replayComplete
