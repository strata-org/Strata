/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata

/-!
## Axioms of the monadic interpreter's headline theorems

Pins the axioms of the soundness and completeness theorems of the monadic interpreter, of Core's
evaluator soundness and of the reference ⇒ engine bridges.  Each depends only on the standard
axioms `propext`, `Classical.choice` and `Quot.sound`.
-/

/--
info: 'Core.core_replaySound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.core_replaySound

/--
info: 'Core.core_replaySound_feasible' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.core_replaySound_feasible

/--
info: 'Core.core_replayComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.core_replayComplete

/--
info: 'Imperative.Calls.call_replaySound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Imperative.Calls.call_replaySound

/--
info: 'Imperative.Calls.call_replaySound_feasible' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Imperative.Calls.call_replaySound_feasible

/--
info: 'Imperative.Calls.call_replayComplete' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Imperative.Calls.call_replayComplete

/--
info: 'Imperative.Calls.call_runInterp_sound' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Imperative.Calls.call_runInterp_sound

/--
info: 'Imperative.Calls.call_runCallInterp_complete' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Imperative.Calls.call_runCallInterp_complete

/--
info: 'Imperative.Calls.genuineFeasible_iff_genuineEnforced' depends on axioms: [propext,
  Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Imperative.Calls.genuineFeasible_iff_genuineEnforced

/--
info: 'Core.boundedEvalSoundAt_of_evalFactoryWF' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.boundedEvalSoundAt_of_evalFactoryWF

/--
info: 'Core.boundedEvalSoundAt_coreFactory' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.boundedEvalSoundAt_coreFactory

/--
info: 'Core.boundedEvalSoundAt_of_userFuncs' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.boundedEvalSoundAt_of_userFuncs

/--
info: 'Core.evalFactoryWF_coreFactory' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.evalFactoryWF_coreFactory

/--
info: 'Core.factoryWF_coreFactory' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.factoryWF_coreFactory

/--
info: 'Lambda.eval_annotateFvars' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Lambda.eval_annotateFvars

/--
info: 'Core.engEvalReach_of_computableEval' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.engEvalReach_of_computableEval

/--
info: 'Core.computableEval_op' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.computableEval_op

/--
info: 'Core.computableEval_userFn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.computableEval_userFn

/--
info: 'Core.computableOp_of_builtin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.computableOp_of_builtin

/--
info: 'Core.writeBackTypedComplete_core' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.writeBackTypedComplete_core

/--
info: 'Core.runChoices_of_evalsComputable' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.runChoices_of_evalsComputable

/--
info: 'Core.core_replayComplete_of_evalsComputable' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.core_replayComplete_of_evalsComputable

/--
info: 'Core.core_replayComplete_of_deterministic_computable' depends on axioms: [propext,
  Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.core_replayComplete_of_deterministic_computable

/--
info: 'Core.core_runCoreInterp_complete_eval_of_computable' depends on axioms: [propext,
  Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.core_runCoreInterp_complete_eval_of_computable

/--
info: 'Core.programInFragment_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.programInFragment_iff

/--
info: 'Core.fragmentExpr_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.fragmentExpr_iff

/--
info: 'Core.evalsComputable_of_inFragment' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.evalsComputable_of_inFragment

/--
info: 'Core.fragmentFactoryWF_of_userFuncs' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.fragmentFactoryWF_of_userFuncs

/--
info: 'Core.fragmentFactoryWF_coreFactory' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.fragmentFactoryWF_coreFactory

/--
info: 'Core.core_replayComplete_of_programInFragment' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.core_replayComplete_of_programInFragment

/--
info: 'Core.core_replayComplete_of_deterministic_programInFragment' depends on axioms: [propext,
  Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.core_replayComplete_of_deterministic_programInFragment

/--
info: 'Core.core_runCoreInterp_complete_eval_of_programInFragment' depends on axioms: [propext,
  Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.core_runCoreInterp_complete_eval_of_programInFragment
