/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.Options
meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

/-! # `deductiveAssumingSatisfiablePaths`

An assertion whose goal evaluates to `false` under assumptions is valid only when its path
condition is contradictory. `deductive` mode asks a solver about that; with
`deductiveAssumingSatisfiablePaths`, whose premise is that every path to an assertion can be
taken, the evaluator reports the assertion failing without one.

The program below has one assertion of each kind: `flag_set` evaluates to `false` on a path
that can be taken, `dead_flag_set` evaluates to `false` on a path that cannot (its premise is
broken on purpose), and `count_nonneg` still needs the solver. -/

meta section
---------------------------------------------------------------------
namespace Strata

def satisfiablePathsPgm :=
#strata
program Core;
datatype Request {
  Request_Cons(count : int, flagged : bool)
};
function count () : int;
inline function unflaggedRequest () : Request {
  Request_Cons(count, false)
}
axiom [count_nonneg_axiom]: int.ge(count, 0);
procedure CheckRequest ()
{
  assume [count_small]: int.le(count, 10);
  // `Request..flagged(unflaggedRequest)` evaluates to `false` whatever `count` is.
  assert [flag_set]: Request..flagged(unflaggedRequest);
  if (int.lt(count, 0)) {
    // The axiom rules this branch out, so `deductive` passes the assertion vacuously.
    assert [dead_flag_set]: Request..flagged(unflaggedRequest);
  }
  assert [count_nonneg]: int.ge(count, 0);
};
#end

-- `deductive` asks the solver about both assertions that evaluate to `false`.
/--
info:
Obligation: flag_set
Property: assert
Result: ❌ fail

Obligation: dead_flag_set
Property: assert
Result: ✅ pass

Obligation: count_nonneg
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify satisfiablePathsPgm (options := Core.VerifyOptions.quiet)

-- Under the premise, both fail during evaluation; only `count_nonneg` reaches the solver.
-- `dead_flag_set` is the failure the premise is responsible for.
/--
info:

Obligation flag_set: failed!

Result obtained during evaluation.


Obligation dead_flag_set: failed!

Result obtained during evaluation.
---
info:
Obligation: flag_set
Property: assert
Result: ❌ fail

Obligation: dead_flag_set
Property: assert
Result: ❌ fail

Obligation: count_nonneg
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify satisfiablePathsPgm
  (options := {Core.VerifyOptions.quiet with checkMode := .deductiveAssumingSatisfiablePaths})

/-! The premise is used for assertions only, and never where the evaluator already sees a
dead path: a cover goes to the solver as in `deductive`, and so does an assertion under an
assumption that is literally `false`. -/

def deadPathsPgm :=
#strata
program Core;
function count () : int;
procedure DeadPaths ()
{
  if (int.lt(count, 0)) {
    if (int.ge(count, 0)) {
      cover [dead_cover]: false;
    }
  }
  if (int.gt(count, 5)) {
    assume [never]: false;
    assert [dead_after_assume_false]: false;
  }
};
#end

/--
info:
Obligation: dead_cover
Property: cover
Result: ❌ fail (❗unreachable in this context)

Obligation: dead_after_assume_false
Property: assert
Result: ✅ pass (❗unreachable in this context)
-/
#guard_msgs in
#eval Core.verify deadPathsPgm
  (options := {Core.VerifyOptions.quiet with
    checkMode := .deductiveAssumingSatisfiablePaths, checkLevel := .full})

/-! At the `full` check level, which also reports reachability, the reachability of an
assertion that evaluates to `false` comes from the premise: `dead_flag_set` is reported
reachable, as the mode assumes every path to an assertion can be taken. -/

/--
info:

Obligation flag_set: failed!

Result obtained during evaluation.


Obligation dead_flag_set: failed!

Result obtained during evaluation.
---
info:
Obligation: flag_set
Property: assert
Result: ❌ always false and is reachable from declaration entry

Obligation: dead_flag_set
Property: assert
Result: ❌ always false and is reachable from declaration entry

Obligation: count_nonneg
Property: assert
Result: ✅ always true and is reachable from declaration entry
-/
#guard_msgs in
#eval Core.verify satisfiablePathsPgm
  (options := {Core.VerifyOptions.quiet with
    checkMode := .deductiveAssumingSatisfiablePaths, checkLevel := .full})

/-! Below, the solver shows that `solver_false` fails on a reachable path, and `cover_false`
is a cover, which the premise never applies to, so both are reported as in `deductive`. -/

def solverDecidedPgm :=
#strata
program Core;
function x () : int;
procedure SolverDecided ()
{
  assume [pos]: int.gt(x, 0);
  assert [solver_false]: int.lt(x, 0);
  cover [cover_false]: int.lt(x, 0);
};
#end

/--
info:
Obligation: solver_false
Property: assert
Result: ❌ always false and is reachable from declaration entry

Obligation: cover_false
Property: cover
Result: ❌ always false and is reachable from declaration entry
-/
#guard_msgs in
#eval Core.verify solverDecidedPgm
  (options := {Core.VerifyOptions.quiet with
    checkMode := .deductiveAssumingSatisfiablePaths, checkLevel := .full})

/-! A path condition that only declares or defines variables is satisfiable, so an assertion
of `false` under it fails without a solver, in `deductive` as in this mode. -/

def definitionsOnlyPgm :=
#strata
program Core;
procedure DefinitionsOnly ()
{
  var y : int := 1;
  assert [defs_only]: false;
};
#end

/--
info:

Obligation defs_only: failed!

Result obtained during evaluation.
---
info:
Obligation: defs_only
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify definitionsOnlyPgm (options := Core.VerifyOptions.quiet)

/--
info:

Obligation defs_only: failed!

Result obtained during evaluation.
---
info:
Obligation: defs_only
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify definitionsOnlyPgm
  (options := {Core.VerifyOptions.quiet with checkMode := .deductiveAssumingSatisfiablePaths})

-- The mode parses from and prints to its name, and counts as deductive.
/-- info: some (Core.VerificationMode.deductiveAssumingSatisfiablePaths) -/
#guard_msgs in
#eval Core.VerificationMode.ofString? "deductiveAssumingSatisfiablePaths"

#guard Core.VerificationMode.deductiveAssumingSatisfiablePaths.toString ==
  "deductiveAssumingSatisfiablePaths"
#guard Core.VerificationMode.deductiveAssumingSatisfiablePaths.isDeductive
#guard Core.VerificationMode.deductive.isDeductive
#guard !Core.VerificationMode.bugFinding.isDeductive
#guard !Core.VerificationMode.bugFindingAssumingCompleteSpec.isDeductive

end Strata
end
