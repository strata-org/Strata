/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Core.Typing.Soundness

/-! # Axioms of the Core typechecker soundness theorems

Each theorem depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`;
a change in the axioms of any of them fails this test. -/

/--
info: 'Core.typeCheck_sound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.typeCheck_sound

/--
info: 'Core.typeCheck_sound_output' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.typeCheck_sound_output

/--
info: 'Core.typeCheck_sound_extraFunctions' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.typeCheck_sound_extraFunctions

/--
info: 'Core.typeCheck_sound_output_extraFunctions' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.typeCheck_sound_output_extraFunctions

/--
info: 'Core.Program.typeCheck_sound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.Program.typeCheck_sound

/--
info: 'Core.Program.typeCheck_sound_output' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.Program.typeCheck_sound_output

/--
info: 'Core.Program.typeCheck.go_sound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.Program.typeCheck.go_sound

/--
info: 'Core.Program.typeCheck.go_sound_output' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.Program.typeCheck.go_sound_output

/--
info: 'Core.Function.typeCheck_sound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.Function.typeCheck_sound

/--
info: 'Core.Function.typeCheck_sound_output' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.Function.typeCheck_sound_output

/--
info: 'Core.Procedure.typeCheck_sound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.Procedure.typeCheck_sound

/--
info: 'Core.Procedure.typeCheck_sound_output' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.Procedure.typeCheck_sound_output

/--
info: 'Core.Statement.typeCheckAux_sound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.Statement.typeCheckAux_sound

/--
info: 'Core.Statement.typeCheck_sound_output' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.Statement.typeCheck_sound_output

/--
info: 'Core.Statement.typeCheckCmd_sound_output' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.Statement.typeCheckCmd_sound_output
