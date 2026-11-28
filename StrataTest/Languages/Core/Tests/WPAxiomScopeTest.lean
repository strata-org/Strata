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
info: p_needs_later_axiom: refuted
q_uses_earlier_axiom: proved
-/
#guard_msgs in
#eval printProved axiomAfterPgm

/--
info: p_needs_later_axiom: refuted
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
info: l_needs_later_axiom: refuted
l_uses_earlier_axiom: proved
l_forall: proved
-/
#guard_msgs in
#eval printProved lemmaPgm

/--
info: l_needs_later_axiom: refuted
l_uses_earlier_axiom: proved
l_forall: proved
-/
#guard_msgs in
#eval printProved lemmaPgm { Core.VerifyOptions.quiet with vcgen := .wp }

/-! A `distinct` declaration is scoped like an axiom: a procedure's or a lemma's obligations
assume exactly the `distinct` facts declared before it, in both modes
(`Core.Specification.AxiomsBeforeProcedureDecl`). `p_needs_later_distinct` and
`l_needs_later_distinct` hold only under the `distinct` declared after them, so they must not
be proved; `q_uses_earlier_distinct` and `l_uses_earlier_distinct`, declared after it, are
proved. -/

def distinctAfterPgm :=
#strata
program Core;

const a : int;
const b : int;

procedure P()
{
  assert [p_needs_later_distinct]: a != b;
};

lemma [l_needs_later_distinct]: a != b;

distinct [ab]: [a, b];

procedure Q()
{
  assert [q_uses_earlier_distinct]: a != b;
};

lemma [l_uses_earlier_distinct]: a != b;

#end

/--
info: p_needs_later_distinct: refuted
l_needs_later_distinct: refuted
q_uses_earlier_distinct: proved
l_uses_earlier_distinct: proved
-/
#guard_msgs in
#eval printProved distinctAfterPgm

/--
info: p_needs_later_distinct: refuted
l_needs_later_distinct: refuted
q_uses_earlier_distinct: proved
l_uses_earlier_distinct: proved
-/
#guard_msgs in
#eval printProved distinctAfterPgm { Core.VerifyOptions.quiet with vcgen := .wp }

/--
info: l_needs_later_distinct: refuted
p_needs_later_distinct: refuted
l_uses_earlier_distinct: proved
q_uses_earlier_distinct: proved
-/
#guard_msgs in
#eval printProved distinctAfterPgm { Core.VerifyOptions.quiet with symExec := some .never }

/-! Two `distinct` declarations interspersed among procedures and lemmas: each obligation
assumes exactly those declared before its procedure or lemma. `P1` and `L1` see neither, `P2`
and `L2` see only `ab`, `P3` and `L3` see both. -/

def twoDistinctsPgm :=
#strata
program Core;

const a : int;
const b : int;
const c : int;

procedure P1()
{
  assert [p1_ab]: a != b;
};

lemma [l1_bc]: b != c;

distinct [ab]: [a, b];

procedure P2()
{
  assert [p2_ab]: a != b;
  assert [p2_bc]: b != c;
};

lemma [l2_bc]: b != c;

distinct [bc]: [b, c];

procedure P3()
{
  assert [p3_ab]: a != b;
  assert [p3_bc]: b != c;
};

lemma [l3_ab_bc]: a != b && b != c;

#end

/--
info: p1_ab: refuted
l1_bc: refuted
p2_ab: proved
p2_bc: refuted
l2_bc: refuted
p3_ab: proved
p3_bc: proved
l3_ab_bc: proved
-/
#guard_msgs in
#eval printProved twoDistinctsPgm

/--
info: p1_ab: refuted
l1_bc: refuted
p2_ab: proved
p2_bc: refuted
l2_bc: refuted
p3_ab: proved
p3_bc: proved
l3_ab_bc: proved
-/
#guard_msgs in
#eval printProved twoDistinctsPgm { Core.VerifyOptions.quiet with vcgen := .wp }

/-! The edges of the placement of `distinct` declarations among the obligations: `ab` comes
before every obligation, `bc` and `cd` have no obligation between them, and `ad` comes after
the last obligation, so no obligation assumes it. `P1` sees only `ab`; `P2` sees `ab`, `bc`
and `cd` but not `ad`. -/

def distinctEdgesPgm :=
#strata
program Core;

const a : int;
const b : int;
const c : int;
const d : int;

distinct [ab]: [a, b];

procedure P1()
{
  assert [e1_ab]: a != b;
  assert [e1_bc]: b != c;
};

distinct [bc]: [b, c];
distinct [cd]: [c, d];

procedure P2()
{
  assert [e2_bc]: b != c;
  assert [e2_cd]: c != d;
  assert [e2_ad]: a != d;
};

distinct [ad]: [a, d];

#end

/--
info: e1_ab: proved
e1_bc: refuted
e2_bc: proved
e2_cd: proved
e2_ad: refuted
-/
#guard_msgs in
#eval printProved distinctEdgesPgm

/--
info: e1_ab: proved
e1_bc: refuted
e2_bc: proved
e2_cd: proved
e2_ad: refuted
-/
#guard_msgs in
#eval printProved distinctEdgesPgm { Core.VerifyOptions.quiet with vcgen := .wp }

/-! A procedure whose paths symbolic evaluation merges out of order: `P2`'s else branch asserts
and exits the labelled block, so its path is merged before the path that reaches `p2_after`.
`P1`'s obligation, deferred before the `distinct`, must stay before it: `p1_needs_later_distinct`
is not proved, and the three assertions of `P2`, after the `distinct`, are proved. -/

def exitReorderPgm :=
#strata
program Core;

const a : int;
const b : int;

procedure P1()
{
  assert [p1_needs_later_distinct]: a != b;
};

distinct [ab]: [a, b];

procedure P2(x : bool)
{
  body: {
    if (x) {
      assert [p2_then]: a != b;
    } else {
      assert [p2_else]: a != b;
      exit body;
    }
    assert [p2_after]: a != b;
  }
};

#end

/--
info: p1_needs_later_distinct: refuted
p2_else: proved
p2_then: proved
p2_after: proved
-/
#guard_msgs in
#eval printProved exitReorderPgm

/-! The same with `--incremental`, which reads the obligation program through its own walk of
the declarations. -/

/--
info: p1_needs_later_distinct: refuted
p2_else: proved
p2_then: proved
p2_after: proved
-/
#guard_msgs in
#eval printProved exitReorderPgm { Core.VerifyOptions.quiet with incremental := true }

/--
info: p1_needs_later_distinct: refuted
p2_then: proved
p2_else: proved
p2_after: proved
-/
#guard_msgs in
#eval printProved exitReorderPgm { Core.VerifyOptions.quiet with vcgen := .wp }

/-! The same in `--vcgen symexec`, with paths kept apart and with paths merged. -/

/--
info: p1_needs_later_distinct: refuted
p2_then: proved
p2_after: proved
p2_else: proved
-/
#guard_msgs in
#eval printProved exitReorderPgm { Core.VerifyOptions.quiet with symExec := some .never }

/--
info: p1_needs_later_distinct: refuted
p2_then: proved
p2_after: proved
p2_else: proved
-/
#guard_msgs in
#eval printProved exitReorderPgm { Core.VerifyOptions.quiet with symExec := some .always }

/-! A pipeline that lists the declaration, WP, SSA and rewrite-loop phases by name
(`Core.nameablePhases`) in place of symbolic evaluation, and drops common-subexpression
elimination, is the order `--vcgen wp` runs, and gives the same verdicts. -/

/-- The default order's phase names with the declaration, WP, SSA and rewrite-loop phases in
    place of symbolic evaluation and without common-subexpression elimination. -/
private def wpPhaseNames : List String :=
  (Core.corePipelinePhases Core.VerifyOptions.quiet).map Core.phaseName |>.flatMap fun n =>
    if n == "symbolicEval" then ["declObligations", "wp", "ssa", "wpLoop"]
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
info: p_needs_later_axiom: refuted
q_uses_earlier_axiom: proved
-/
#guard_msgs in
#eval namedWPVerdicts

/-! A `distinct` declaration over one constant holds trivially: it is accepted, and it does
not make the constant differ from another one. -/

def oneDistinctPgm :=
#strata
program Core;

const a : int;
const b : int;

distinct [justA]: [a];

procedure P()
{
  assert [p_refl]: a == a;
  assert [p_ab]: a != b;
};

#end

/--
info: p_refl: proved
p_ab: refuted
-/
#guard_msgs in
#eval printProved oneDistinctPgm

/--
info: p_refl: proved
p_ab: refuted
-/
#guard_msgs in
#eval printProved oneDistinctPgm { Core.VerifyOptions.quiet with vcgen := .wp }

end Strata.WPAxiomScopeTest
