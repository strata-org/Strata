/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Transform.Simplify.StmtShape
import Strata.Transform.Simplify.DeadDefsShape
import Strata.Transform.Simplify.LiveSweep

/-! # The syntactic layer of the Simplify proof rests on no `sorry`

Pins the axioms of the main results about the shape of Simplify's statement traversal
and of its dead-definition sweep, so that a `sorry` or a new axiom in any of them fails
this test. -/

namespace Core.Simplify

/-- info: 'Core.Simplify.simpStmts_writes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms simpStmts_writes

/-- info: 'Core.Simplify.simpStmts_values_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms simpStmts_values_sub

/-- info: 'Core.Simplify.simpStmts_nodupKeys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms simpStmts_nodupKeys

/-- info: 'Core.Simplify.mem_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_join

/-- info: 'Core.Simplify.dropDeadDefsStmt_ite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dropDeadDefsStmt_ite

/-- info: 'Core.Simplify.live_dropDeadDefsAux_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms live_dropDeadDefsAux_mono

/-- info: 'Core.Simplify.Defined.ofParams_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Defined.ofParams_spec

/-- info: 'Core.Simplify.mem_dropDeadDefsAux_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_dropDeadDefsAux_live

/-- info: 'Core.Simplify.dropDeadDefsStmt_ite_arms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dropDeadDefsStmt_ite_arms

/-- info: 'Core.Simplify.dropDeadDefsArms_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dropDeadDefsArms_spec

/-- info: 'Core.Simplify.dropDeadDefsAux_inserted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dropDeadDefsAux_inserted

/-- info: 'Core.Simplify.mem_invalidate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_invalidate

end Core.Simplify
