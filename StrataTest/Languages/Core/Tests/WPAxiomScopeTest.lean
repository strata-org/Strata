/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier
import Strata.Languages.Core
import Strata.MetaVerifier
import StrataTest.Languages.Core.Tests.WPTestUtils

/-! # Axiom scope of the obligation program of the WP and SSA phases

A procedure's obligations assume exactly the axioms declared before it, in symbolic mode
and in `--vcgen wp` alike: the declaration phase keeps the source program's relative order of
axioms, procedures and lemmas (`WP.declObligationsProgramWith`, checked by
`WP.axiomScopesAgree`), and the WP and SSA phases keep the order of the declarations. Here
`P`'s assertion holds only under the axiom declared after `P`, so it must not be proved; `Q`,
declared after the axiom, is proved. -/

namespace Strata.WPAxiomScopeTest

open Strata.WPTestUtils

def axiomAfterPgm :=
#strata
program Core;

function R(x: int): bool;

procedure P()
{
  assert [p_needs_later_axiom]: R(1);
};

axiom [allR]: (forall y : int :: R(y));

procedure Q()
{
  assert [q_uses_earlier_axiom]: R(2);
};

#end

/--
info: p_needs_later_axiom: not proved
q_uses_earlier_axiom: proved
-/
#guard_msgs in
#eval printProved axiomAfterPgm

/--
info: p_needs_later_axiom: not proved
q_uses_earlier_axiom: proved
-/
#guard_msgs in
#eval printProved axiomAfterPgm { Core.VerifyOptions.quiet with vcgen := .wp }

/-! A lemma is checked under exactly the axioms declared before it, in both modes: the
obligation program states each lemma's obligation, as symbolic evaluation states it, in an
obligation unit at the lemma's position (`WP.lemmaUnit`). `l_needs_later_axiom` holds
only under the axiom declared after it, so it must not be proved; `l_uses_earlier_axiom` and the
quantified `l_forall` are proved. -/

def lemmaPgm :=
#strata
program Core;

function R(x: int): bool;

lemma [l_needs_later_axiom]: R(1);

axiom [allR]: (forall y : int :: R(y));

lemma [l_uses_earlier_axiom]: R(2);
lemma [l_forall]: forall x : int :: R(x);

#end

/--
info: l_needs_later_axiom: not proved
l_uses_earlier_axiom: proved
l_forall: proved
-/
#guard_msgs in
#eval printProved lemmaPgm

/--
info: l_needs_later_axiom: not proved
l_uses_earlier_axiom: proved
l_forall: proved
-/
#guard_msgs in
#eval printProved lemmaPgm { Core.VerifyOptions.quiet with vcgen := .wp }

/-! A pipeline that lists the declaration, WP, SSA and dead-definition phases by name
(`Core.nameablePhases`) in place of symbolic evaluation is the order `--vcgen wp` runs, and
gives the same verdicts. -/

/-- The default order's phase names with the declaration, WP, SSA and dead-definition phases in
    place of symbolic evaluation and no common-subexpression elimination. -/
private def wpPhaseNames : List String :=
  (Core.corePipelinePhases Core.VerifyOptions.quiet).map Core.phaseName |>.flatMap fun n =>
    if n == "symbolicEval" then ["declObligations", "wp", "ssa", "deadDefElim"]
    else if n == "commonSubexprElim" then [] else [n]

/-- info: true -/
#guard_msgs in
#eval wpPhaseNames ==
  (Core.corePipelinePhases { Core.VerifyOptions.quiet with vcgen := .wp }).map
      Core.phaseName

private def namedWPVerdicts : IO Unit := do
  let opts := Core.VerifyOptions.quiet
  let phases ← IO.ofExcept (Core.resolvePhases (Core.nameablePhases opts) wpPhaseNames)
  let vp ← IO.ofExcept (Core.validatePipeline phases)
  printProved axiomAfterPgm opts (pipeline := some vp)

/--
info: p_needs_later_axiom: not proved
q_uses_earlier_axiom: proved
-/
#guard_msgs in
#eval namedWPVerdicts

end Strata.WPAxiomScopeTest
