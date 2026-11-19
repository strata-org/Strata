/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

/-! # A lemma is never assumed by the lemmas after it

Deductive verification checks each lemma under the axioms and `distinct` declarations before it,
never under the lemmas before it: a lemma raises only an assert event (`declEvents`). Proof
obligation generation does the same, in every mode. Here `L1` does not follow from the
declarations before it and `L2` follows from `L1` alone, so both fail; a back end that assumed `L1`
while checking `L2` would report `L2` passing, a verdict deductive verification does not support.
A lemma that does hold is still proved (`L0`). A lemma the solver can neither prove nor refute is
not assumed either, and a false claim stated as an axiom, which is assumed, does prove the later
lemma, so the tests detect assumption.
-/

meta section

namespace Core.LemmaNotAssumedTests

private def pgm :=
#strata
program Core;
function P(x : int) : bool;
lemma [L0]: forall x : int :: x == x;
lemma [L1]: forall x : int :: P(x);
lemma [L2]: P(3);
#end

private def verdicts (o : Core.VerifyOptions) : IO Unit := do
  for r in ← Strata.Core.verify pgm (options := o) do
    IO.println s!"{r.obligation.label}: {r.formatOutcome}"

/--
info: L0: ✅ pass
L1: ❌ fail
L2: ❌ fail
-/
#guard_msgs in
#eval verdicts .quiet

/--
info: L0: ✅ pass
L1: ❌ fail
L2: ❌ fail
-/
#guard_msgs in
#eval verdicts { Core.VerifyOptions.quiet with vcgen := .wp }

/--
info: L0: ✅ pass
L1: ❌ fail
L2: ❌ fail
-/
#guard_msgs in
#eval verdicts { Core.VerifyOptions.quiet with incremental := true }

/--
info: L0: ✅ pass
L1: ❌ fail
L2: ❌ fail
-/
#guard_msgs in
#eval verdicts { Core.VerifyOptions.quiet with symExec := some .never }

/--
info: L0: ✅ pass
L1: ❌ fail
L2: ❌ fail
-/
#guard_msgs in
#eval verdicts { Core.VerifyOptions.quiet with symExec := some .always }

/-- The proof-obligation modes: symbolic evaluation, `--vcgen wp`, `--incremental`, and
    `--vcgen symexec` both per path and with paths merged. -/
private def allModes : List (String × Core.VerifyOptions) :=
  [("symbolic", .quiet),
   ("wp", { Core.VerifyOptions.quiet with vcgen := .wp }),
   ("incremental", { Core.VerifyOptions.quiet with incremental := true }),
   ("symexec:per-path", { Core.VerifyOptions.quiet with symExec := some .never }),
   ("symexec:merged", { Core.VerifyOptions.quiet with symExec := some .always })]

/-- Prints, for each of `allModes`, one line `mode: ` followed by `label verdict` for every
    obligation of `p`, the verdict being `proved`, `failed` or `unknown`. -/
private def printAllModesVerdicts (p : StrataDDM.SourcedProgram) : IO Unit := do
  for (mode, opts) in allModes do
    let rs ← Strata.Core.verify p (options := opts)
    let vs := rs.toList.map fun r =>
      let v := if r.isSuccess then "proved" else if r.isFailure then "failed" else "unknown"
      s!"{r.obligation.label} {v}"
    IO.println s!"{mode}: {", ".intercalate vs}"

/-! `l1` is neither proved nor refuted: with a quantified axiom in scope the solver answers
unknown. `l2` follows from `l1`, and stays unknown too. -/

private def unknownLemmaPgm :=
#strata
program Core;

function f(x : int) : int;

axiom [ax] (x : int) { f(x) }: int.gt(f(x), int.sub(0, 10));

lemma [l1] (x : int) { f(x) }: int.gt(f(x), 0);
lemma [l2]: int.gt(f(3), 0);

#end

/--
info: symbolic: l1 unknown, l2 unknown
wp: l1 unknown, l2 unknown
incremental: l1 unknown, l2 unknown
symexec:per-path: l1 unknown, l2 unknown
symexec:merged: l1 unknown, l2 unknown
-/
#guard_msgs in
#eval printAllModesVerdicts unknownLemmaPgm

/-! The control: a false claim stated as an axiom is assumed, so it proves `l2`. The same claim
as a lemma does not, which is what the tests above check. -/

private def falseAxiomPgm :=
#strata
program Core;

function f(x : int) : int;

axiom [a1]: forall x : int :: int.gt(x, x);

lemma [l2]: int.gt(f(3), 0);

#end

/--
info: symbolic: l2 proved
wp: l2 proved
incremental: l2 proved
symexec:per-path: l2 proved
symexec:merged: l2 proved
-/
#guard_msgs in
#eval printAllModesVerdicts falseAxiomPgm

end Core.LemmaNotAssumedTests

end
