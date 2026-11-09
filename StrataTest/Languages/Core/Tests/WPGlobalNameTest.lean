/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier
import Strata.Languages.Core
import Strata.MetaVerifier
import StrataTest.Languages.Core.Tests.WPTestUtils

/-! # Parameters named like global functions and constants

A variable of an obligation and a function of the program are both encoded as SMT
constants under their own names, so an obligation variable named like a 0-ary function or
a constant would denote it, constrained by its axioms. The SSA phase gives every
parameter a fresh entry name, as symbolic evaluation does, so a read-only parameter `c` never
denotes a global `c`. Each assertion below holds only of the global `c` (axiom `c0`), not of an
arbitrary parameter `c`, so it must not be proved, in symbolic mode and in
`--vcgen wp` alike. -/

namespace Strata.WPGlobalNameTest

open Strata.WPTestUtils

/-- A read-only parameter named like a 0-ary function. -/
def functionPgm :=
#strata
program Core;

function c() : int;
axiom [c0]: c == 0;

procedure P(c : int, out r : int)
{
  assert [pc]: c == 0;
};

#end

/-- A read-only parameter named like a constant. -/
def constPgm :=
#strata
program Core;

const c : int;
axiom [c0]: c == 0;

procedure P(c : int, out r : int)
{
  assert [pc]: c == 0;
};

#end

/-- An output parameter assigned from the read-only parameter named like a 0-ary function. -/
def assignPgm :=
#strata
program Core;

function c() : int;
axiom [c0]: c == 0;

procedure P(c : int, out r : int)
{
  r := c;
  assert [pr]: r == 0;
};

#end

/--
info: symbolic pc: not proved
wp pc: not proved
-/
#guard_msgs in
#eval printModesProved functionPgm

/--
info: symbolic pc: not proved
wp pc: not proved
-/
#guard_msgs in
#eval printModesProved constPgm

/--
info: symbolic pr: not proved
wp pr: not proved
-/
#guard_msgs in
#eval printModesProved assignPgm

/-! Common-subexpression elimination prepends its definitions to a body, so it requires a
body that declares no variable (`noInits`), which symbolic evaluation establishes and the
SSA phase does not. A pipeline that runs it after the WP, SSA and dead-definition phases is
rejected. -/

/-- The phase names of the `--vcgen wp` order, with `commonSubexprElim` at the end. -/
private def wpThenCSE : List String :=
  (Core.corePipelinePhases { Core.VerifyOptions.quiet with vcgen := .wp }).map
    Core.phaseName ++ ["commonSubexprElim"]

/-- `validatePipeline` on the phases named `names`: `accepted`, or its diagnostic. -/
private def validation (names : List String) : Except String String := do
  let phases ← Core.resolvePhases (Core.nameablePhases Core.VerifyOptions.quiet) names
  match Core.validatePipeline phases with
  | .ok _ => pure "accepted"
  | .error e => pure e

/--
info: Except.ok "phase #18 `commonSubexprElim` requires `noInits` but preceding phases only guarantee `noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, hasObligationForm, noProcedureContracts, noPolymorphicProcedures, noPolymorphicFunctions, typeAnnotated, exitsCovered, armsHaveObligations`"
-/
#guard_msgs in
#eval validation wpThenCSE

/-! The phases a caller may name do not depend on `--vcgen`: resolved against the phases
nameable under `--vcgen wp`, the same list is rejected with the same diagnostic. -/

/--
info: Except.ok "phase #18 `commonSubexprElim` requires `noInits` but preceding phases only guarantee `noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, hasObligationForm, noProcedureContracts, noPolymorphicProcedures, noPolymorphicFunctions, typeAnnotated, exitsCovered, armsHaveObligations`"
-/
#guard_msgs in
#eval show Except String String from do
  let opts := { Core.VerifyOptions.quiet with vcgen := .wp }
  let phases ← Core.resolvePhases (Core.nameablePhases opts) wpThenCSE
  match Core.validatePipeline phases with
  | .ok _ => pure "accepted"
  | .error e => pure e

/-- info: Except.ok "accepted" -/
#guard_msgs in
#eval validation ((Core.corePipelinePhases Core.VerifyOptions.quiet).map Core.phaseName)

end Strata.WPGlobalNameTest
