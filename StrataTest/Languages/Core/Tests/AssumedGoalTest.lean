/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier
import Strata.Languages.Core
import Strata.MetaVerifier

/-! # Goals that the assumptions of their own path decide, without a solver

The verifier runs with a solver binary that does not exist, so an obligation is settled only if
the evaluator settles it. In symbolic mode and under `--vcgen wp`: a goal equal, up to metadata,
to an assumption on its path is proved; a cover whose goal is the negation of an assumption on
its path, or whose path assumes the negation of its goal, is refuted; and a cover on a path
with a literally `false` assumption is refuted. -/

namespace Strata.AssumedGoalTest

/-- Assertions of assumed facts: one about an input, after an unrelated assignment, and one about
    an assigned variable. -/
def assumedPgm :=
#strata
program Core;
procedure P(x : int, out y : int)
{
  assume [pos]: (int.gt(x, 0));
  y := int.add(x, 1);
  assert [assumedInput]: (int.gt(x, 0));
  assume [big]: (int.gt(y, 1));
  assert [assumedAssigned]: (int.gt(y, 1));
};
#end

/-- Covers that the path decides: the negation of an assumed fact, a fact whose negation is
    assumed, and a cover after a literally `false` assumption. -/
def refutedCoverPgm :=
#strata
program Core;
procedure P(x : int)
{
  assume [pos]: (int.gt(x, 0));
  cover [negOfAssumed]: !(int.gt(x, 0));
};
procedure R(x : int)
{
  assume [notPos]: !(int.gt(x, 0));
  cover [assumedNeg]: (int.gt(x, 0));
};
procedure Q(x : int)
{
  assume [dead]: false;
  cover [deadCover]: (int.gt(x, 0));
};
#end

/-- Prints, per cover, `unreachable` when the evaluator decides its path unreachable, `refuted`
    when it decides the goal false, `reachable` for any other settled outcome, and `left to the
    solver` when it needs the solver, which cannot be started, for symbolic evaluation and
    `--vcgen wp`. -/
def printCoversWithoutSolver : IO Unit := do
  let noSolver := { Core.VerifyOptions.quiet with solver := "/nonexistent/strata-test-solver" }
  for (mode, opts) in [("symbolic", noSolver), ("wp", { noSolver with vcgen := .wp })] do
    for r in ← Core.verify refutedCoverPgm (options := opts) do
      let verdict := match r.outcome with
        | .ok _ =>
          if r.isUnreachable then "unreachable" else if r.isFailure then "refuted" else "reachable"
        | .error _ => "left to the solver"
      IO.println s!"{mode} {r.obligation.label}: {verdict}"

/-- Prints `mode label: proved` or `mode label: not proved` per obligation, for symbolic
    evaluation and `--vcgen wp`, with a solver that cannot be started. -/
def printWithoutSolver : IO Unit := do
  let noSolver := { Core.VerifyOptions.quiet with solver := "/nonexistent/strata-test-solver" }
  for (mode, opts) in [("symbolic", noSolver), ("wp", { noSolver with vcgen := .wp })] do
    for r in ← Core.verify assumedPgm (options := opts) do
      IO.println s!"{mode} {r.obligation.label}: {if r.isSuccess then "proved" else "not proved"}"

/--
info: symbolic assumedInput: proved
symbolic assumedAssigned: proved
wp assumedInput: proved
wp assumedAssigned: proved
-/
#guard_msgs in
#eval printWithoutSolver

/--
info: symbolic negOfAssumed: refuted
symbolic assumedNeg: refuted
symbolic deadCover: refuted
wp negOfAssumed: refuted
wp assumedNeg: refuted
wp deadCover: refuted
-/
#guard_msgs in
#eval printCoversWithoutSolver

end Strata.AssumedGoalTest
