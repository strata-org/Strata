/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier
import Strata.Languages.Core
import Strata.MetaVerifier
import StrataTest.Languages.Core.Tests.WPTestUtils
import StrataTest.Languages.Core.Tests.ReparseTestUtils

/-! # Verdicts on paths through loop elimination's arbitrary iteration

Loop elimination replaces a loop by one arbitrary iteration from a havocked state, and marks the
paths through that iteration with an assumption of the guard (`$__loopElimAssume_guard_N`). A
counterexample on such a path comes from the havocked state, not from an execution, so loop
elimination's model check reports it as `unknown`.

When the guard is `true`, as in a loop left by an `exit`, symbolic evaluation keeps the marker in
the path condition (`EvalContext.keepsTrueAssume`), and so do the SSA phase of `--vcgen wp`
(`WPOps.keepsTrueAssume`) and symbolic execution (`--vcgen symexec`, `SymExec.assumeCond`); when
the guard is nondeterministic, loop elimination marks the entered and the left guard with an
assumption of `true`. So a counterexample through the arbitrary iteration is `unknown` in every
mode. A counterexample on a path through no abstraction stays a failure. The invariant
assumptions that the insertion of loop invariant checks adds before and after a loop are
abstraction markers too (`$__insertLoopInvAssume_`), on every path that passes the loop, the path
that skips it included. Symbolic execution's per-path mode (`MergeMode.never`) keeps the paths
apart, so a path that skips a loop with no invariant carries no marker. -/

namespace Strata.LoopElimMarkerTest

open Strata.WPTestUtils

/-- The `modes` of `WPTestUtils`, symbolic execution (`--vcgen symexec`) and its per-path mode
    (`--vcgen symexec:per-path`, which never merges paths), each with its name. -/
def markerModes : List (String × Core.VerifyOptions) :=
  modes ++ [("symexec", { Core.VerifyOptions.quiet with symExec := some .default }),
    ("per-path", { Core.VerifyOptions.quiet with symExec := some .never })]

/-- Prints, for each of the `markerModes`, one line `mode: ` followed by `label verdict` for every
    obligation of `pgm`, comma-separated, the verdict being `proved`, `failed` or `unknown`. -/
def printMarkerVerdicts (pgm : StrataDDM.SourcedProgram) : IO Unit := do
  for (mode, opts) in markerModes do
    let rs ← Core.verify pgm (options := opts)
    let vs := rs.toList.map fun r =>
      let v := if r.isSuccess then "proved" else if r.isFailure then "failed" else "unknown"
      s!"{r.obligation.label} {v}"
    IO.println s!"{mode}: {", ".intercalate vs}"

/-- `p` with the bodies of the procedures named in `names` marked opaque (`Body.isOpaque`). -/
def markOpaque (names : List String) (p : Core.Program) : Core.Program :=
  { p with decls := p.decls.map fun
    | .proc q md =>
      if names.contains q.header.name.name then
        .proc { q with body := match q.body with
          | .structured ss _ => .structured ss true
          | .cfg g _ => .cfg g true
          | .abstract => .abstract } md
      else .proc q md
    | d => d }

/-- `printMarkerVerdicts` on `pgm` with the bodies of the procedures `names` marked opaque. -/
def printOpaqueMarkerVerdicts (names : List String) (pgm : StrataDDM.SourcedProgram) :
    IO Unit := do
  let program ← IO.ofExcept (strataProgramToCore pgm.program)
  for (mode, opts) in markerModes do
    let rs ← (Core.verifyProgram (markOpaque names program) opts).toIO IO.userError
    let vs := rs.toList.map fun r =>
      let v := if r.isSuccess then "proved" else if r.isFailure then "failed" else "unknown"
      s!"{r.obligation.label} {v}"
    IO.println s!"{mode}: {", ".intercalate vs}"

/-- A `while (true)` loop left by an `exit` when its condition fails: the only path to
    `sum_is_10` leaves the arbitrary iteration with havocked `sum` and `i`, so its counterexample
    (`i = 5`, `sum = 0`) is not one of an execution, in which `sum` is `10`. -/
def whileTruePgm :=
#strata
program Core;
procedure Sum(out sum : int)
{
  var i : int;
  sum := 0;
  i := 1;
  loop_0: {
    while (true) {
      if (int.le(i, 4)) {
        sum := int.add(sum, i);
        i := int.add(i, 1);
      } else {
        exit loop_0;
      }
    }
  }
  assert [sum_is_10]: sum == 10;
};
#end

/-- info: symbolic: sum_is_10 unknown
wp: sum_is_10 unknown
symexec: sum_is_10 unknown
per-path: sum_is_10 unknown -/
#guard_msgs in
#eval printMarkerVerdicts whileTruePgm

/-- A `for` loop as a `while (true)` loop whose body starts with the exit test: `i` is `5` after
    every execution, and the counterexample to `i_is_5` comes from the arbitrary iteration. -/
def bareForPgm :=
#strata
program Core;
procedure Count(out i : int)
{
  i := 0;
  loop_0: {
    while (true) {
      if (!(int.lt(i, 5))) {
        exit loop_0;
      }
      i := int.add(i, 1);
    }
  }
  assert [i_is_5]: i == 5;
};
#end

/-- info: symbolic: i_is_5 unknown
wp: i_is_5 unknown
symexec: i_is_5 unknown
per-path: i_is_5 unknown -/
#guard_msgs in
#eval printMarkerVerdicts bareForPgm

/-- An assertion inside the body of a `while (true)` loop, reached through the arbitrary
    iteration: the marker of the entered guard is on its path in every mode, the SSA phase
    of `--vcgen wp` and symbolic execution keeping it as symbolic evaluation does. -/
def insideLoopPgm :=
#strata
program Core;
procedure Sum(out sum : int)
{
  var i : int;
  sum := 0;
  i := 1;
  loop_0: {
    while (true) {
      if (int.le(i, 4)) {
        assert [sum_le_10]: int.le(sum, 10);
        sum := int.add(sum, i);
        i := int.add(i, 1);
      } else {
        exit loop_0;
      }
    }
  }
};
#end

/-- info: symbolic: sum_le_10 unknown
wp: sum_le_10 unknown
symexec: sum_le_10 unknown
per-path: sum_le_10 unknown -/
#guard_msgs in
#eval printMarkerVerdicts insideLoopPgm

/-- A loop with a nondeterministic guard, left by an `exit`: loop elimination marks the entered
    and the left guard with an assumption of `true`, so the counterexample from the arbitrary
    iteration is reported as `unknown`. Every execution leaves the loop with `i = 5`. -/
def nondetGuardPgm :=
#strata
program Core;
procedure Count(out i : int)
{
  i := 0;
  loop_0: {
    while *
    {
      if (int.ge(i, 5)) {
        exit loop_0;
      }
      i := int.add(i, 1);
    }
  }
  assert [i_le_5]: int.le(i, 5);
};
#end

/-- info: symbolic: i_le_5 unknown
wp: i_le_5 unknown
symexec: i_le_5 unknown
per-path: i_le_5 unknown -/
#guard_msgs in
#eval printMarkerVerdicts nondetGuardPgm

/-- An assertion before a `while (true)` loop fails on a path through no abstraction: its
    counterexample (`x = 1`) is one of an execution. -/
def realFailPgm :=
#strata
program Core;
procedure Real(x : int, out y : int)
{
  assume (int.gt(x, 0));
  assert [x_gt_1]: int.gt(x, 1);
  y := 0;
  loop_0: {
    while (true) {
      if (int.ge(y, x)) {
        exit loop_0;
      }
      y := int.add(y, 1);
    }
  }
};
#end

/-- info: symbolic: x_gt_1 failed
wp: x_gt_1 failed
symexec: x_gt_1 failed
per-path: x_gt_1 failed -/
#guard_msgs in
#eval printMarkerVerdicts realFailPgm

/-! Call elimination marks the postcondition assumptions of every call to a procedure with a
body, with or without outputs: the contract over-approximates the callee, which may not return in
every state the contract admits. A call to an abstract procedure is not marked
(`callElimPostPrefix`): its contract is its call semantics. -/

/-- A call without outputs whose contract is `ensures true`, then an assertion that fails for
    `x = 0`: the path goes through the callee's contract, so the verdict is `unknown`. -/
def noOutputCallPgm :=
#strata
program Core;
procedure Q (x : int)
spec { ensures true; }
{ };
procedure P (x : int)
{
  call Q(x);
  assert [x_pos]: int.gt(x, 0);
};
#end

/-- info: symbolic: Q_ensures_0 proved, x_pos unknown
wp: Q_ensures_0 proved, x_pos unknown
symexec: Q_ensures_0 proved, x_pos unknown
per-path: Q_ensures_0 proved, x_pos unknown -/
#guard_msgs in
#eval printMarkerVerdicts noOutputCallPgm

/-- A call without outputs to a callee that returns only when `x > 1000`, under the contract
    `x > 100`: the counterexample `x = 150` to `x_big` satisfies the contract but no execution
    returns from the call in it. -/
def blockingCalleePgm :=
#strata
program Core;
procedure Q (x : int)
spec { ensures [q_post]: int.gt(x, 100); }
{ assume int.gt(x, 1000); };
procedure P (x : int)
{
  call Q(x);
  assert [x_big]: int.gt(x, 200);
};
#end

/-- info: symbolic: q_post proved, x_big unknown
wp: q_post proved, x_big unknown
symexec: q_post proved, x_big unknown
per-path: q_post proved, x_big unknown -/
#guard_msgs in
#eval printMarkerVerdicts blockingCalleePgm

/-- A call whose `inout` argument is havocked under the contract `ensures true`: `a` is `4`
    after every execution, and the counterexample to `ok` comes from the havocked output. -/
def havocCallPgm :=
#strata
program Core;
procedure q (inout n : int)
spec { ensures true; }
{
  n := int.add(n, 1);
};
procedure p ()
{
  var a : int := 3;
  call q(inout a);
  assert [ok]: int.ge(a, 0);
};
#end

/-- info: symbolic: q_ensures_0 proved, ok unknown
wp: q_ensures_0 proved, ok unknown
symexec: q_ensures_0 proved, ok unknown
per-path: q_ensures_0 proved, ok unknown -/
#guard_msgs in
#eval printMarkerVerdicts havocCallPgm

/-- The call of `havocCallPgm` to an abstract `q`: a call to `q` havocs `n` under `ensures true`,
    so `a = -1` after the call is a state of an execution and `ok` fails. -/
def abstractCallPgm :=
#strata
program Core;
procedure q (inout n : int)
spec { ensures true; };
procedure p ()
{
  var a : int := 3;
  call q(inout a);
  assert [ok]: int.ge(a, 0);
};
#end

/-- info: symbolic: ok failed
wp: ok failed
symexec: ok failed
per-path: ok failed -/
#guard_msgs in
#eval printMarkerVerdicts abstractCallPgm

/-- The call of `abstractCallPgm` to a `q` with the body `{ }`, which does nothing: call elimination
    still replaces the call by the contract, which havocs `n`, so the path is marked and `ok` is
    `unknown`, although `a` is `3` after every execution. -/
def emptyBodyCallPgm :=
#strata
program Core;
procedure q (inout n : int)
spec { ensures true; }
{ };
procedure p ()
{
  var a : int := 3;
  call q(inout a);
  assert [ok]: int.ge(a, 0);
};
#end

/-- info: symbolic: q_ensures_0 proved, ok unknown
wp: q_ensures_0 proved, ok unknown
symexec: q_ensures_0 proved, ok unknown
per-path: q_ensures_0 proved, ok unknown -/
#guard_msgs in
#eval printMarkerVerdicts emptyBodyCallPgm

/-- A call to a procedure with a body and no postconditions: call elimination marks the havocs
    of its output with an assumption of `true`, as if the callee had `ensures true`. `g` sets `r`
    to `1`, so `y_is_1` holds after every execution, and its counterexample (`y = 0`) comes from
    the havocked output. `x_pos`, before the call, fails on a path through no abstraction. -/
def noPostcondCallPgm :=
#strata
program Core;
procedure g (out r : int)
{
  r := 1;
};
procedure p (x : int, out y : int)
{
  assert [x_pos]: int.gt(x, 0);
  call g(out y);
  assert [y_is_1]: y == 1;
};
#end

/-- info: symbolic: x_pos failed, y_is_1 unknown
wp: x_pos failed, y_is_1 unknown
symexec: x_pos failed, y_is_1 unknown
per-path: x_pos failed, y_is_1 unknown -/
#guard_msgs in
#eval printMarkerVerdicts noPostcondCallPgm

/-- The call of `noPostcondCallPgm` to a `g` whose body is the stub `assume true`, the shape a
    front end uses for a callee it does not want read as abstract: `g` has a body, so the call is
    marked and `y_is_1` is `unknown`. -/
def stubBodyNoPostcondCallPgm :=
#strata
program Core;
procedure g (out r : int)
{
  assume true;
};
procedure p (x : int, out y : int)
{
  assert [x_pos]: int.gt(x, 0);
  call g(out y);
  assert [y_is_1]: y == 1;
};
#end

/-- info: symbolic: x_pos failed, y_is_1 unknown
wp: x_pos failed, y_is_1 unknown
symexec: x_pos failed, y_is_1 unknown
per-path: x_pos failed, y_is_1 unknown -/
#guard_msgs in
#eval printMarkerVerdicts stubBodyNoPostcondCallPgm

/-- The call of `noPostcondCallPgm` to a `g` whose body havocs its output: the call is marked, as
    for every callee with a body that is not opaque, and `y_is_1` is `unknown`. -/
def havocBodyNoPostcondCallPgm :=
#strata
program Core;
procedure g (out r : int)
{
  havoc r;
};
procedure p (x : int, out y : int)
{
  assert [x_pos]: int.gt(x, 0);
  call g(out y);
  assert [y_is_1]: y == 1;
};
#end

/-- info: symbolic: x_pos failed, y_is_1 unknown
wp: x_pos failed, y_is_1 unknown
symexec: x_pos failed, y_is_1 unknown
per-path: x_pos failed, y_is_1 unknown -/
#guard_msgs in
#eval printMarkerVerdicts havocBodyNoPostcondCallPgm

/-- Calls on one branch of a fork to a `g` without postconditions. `--vcgen wp` keeps the marker
    of the havoc under the reach condition of its branch (`WP.kMarkImp`). In `p` and `q`, every
    counterexample to `x_pos` lies on the branch without the call, so it falsifies that condition
    and the failure stands. In `r` and `s`, every counterexample to `y_is_1` passes the call, so
    it is unknown. Symbolic evaluation and symbolic execution keep the marker on both branches,
    so `x_pos` is unknown there. -/
def branchCallPgm :=
#strata
program Core;
procedure g (out r : int)
{
  r := 1;
};
procedure p (b : bool, out y : int, out x : int)
{
  if (b) { call g(out y); x := 1; } else { x := 0; }
  assert [x_pos]: int.gt(x, 0);
};
procedure q (b : bool, out y : int, out x : int)
{
  if (b) { x := 0; } else { call g(out y); x := 1; }
  assert [x_pos]: int.gt(x, 0);
};
procedure r (b : bool, out y : int)
{
  if (b) { call g(out y); } else { y := 1; }
  assert [y_is_1]: y == 1;
};
procedure s (b : bool, out y : int)
{
  if (b) { y := 1; } else { call g(out y); }
  assert [y_is_1]: y == 1;
};
#end

/-- info: symbolic: x_pos unknown, x_pos unknown, y_is_1 unknown, y_is_1 unknown
wp: x_pos failed, x_pos failed, y_is_1 unknown, y_is_1 unknown
symexec: x_pos unknown, x_pos unknown, y_is_1 unknown, y_is_1 unknown
per-path: x_pos failed, x_pos failed, y_is_1 unknown, y_is_1 unknown -/
#guard_msgs in
#eval printMarkerVerdicts branchCallPgm

/-- The branches of `branchCallPgm` with the call replaced by a call to an abstract `ext` and the
    marker a front end places after a call to a procedure that models code Strata does not see
    (`Core.externalAssumePrefix`). The verdicts are those of `branchCallPgm`. -/
def branchExternalPgm :=
#strata
program Core;
procedure ext (out r : int);
procedure p (b : bool, out y : int, out x : int)
{
  if (b) { call ext(out y); assume [$__externalAssume_0]: true; x := 1; } else { x := 0; }
  assert [x_pos]: int.gt(x, 0);
};
procedure q (b : bool, out y : int, out x : int)
{
  if (b) { x := 0; } else { call ext(out y); assume [$__externalAssume_1]: true; x := 1; }
  assert [x_pos]: int.gt(x, 0);
};
procedure r (b : bool, out y : int)
{
  if (b) { call ext(out y); assume [$__externalAssume_2]: true; } else { y := 1; }
  assert [y_is_1]: y == 1;
};
procedure s (b : bool, out y : int)
{
  if (b) { y := 1; } else { call ext(out y); assume [$__externalAssume_3]: true; }
  assert [y_is_1]: y == 1;
};
#end

/-- info: symbolic: x_pos unknown, x_pos unknown, y_is_1 unknown, y_is_1 unknown
wp: x_pos failed, x_pos failed, y_is_1 unknown, y_is_1 unknown
symexec: x_pos unknown, x_pos unknown, y_is_1 unknown, y_is_1 unknown
per-path: x_pos failed, x_pos failed, y_is_1 unknown, y_is_1 unknown -/
#guard_msgs in
#eval printMarkerVerdicts branchExternalPgm

/-- A marker under a reach condition that divides by zero. Core gives `x / 0.0` the value `0.0`,
    while the solver leaves it unconstrained, so the two can disagree on the condition
    `x / 0.0 > 0.0`. The counterexample to `y_is_1` takes the branch with the call, where the
    solver makes the condition true, and is `unknown` in every mode: the model check evaluates
    no condition or definition with a division (`Core.markerGuardEvaluable`), so the marker
    applies. -/
def divByZeroGuardPgm :=
#strata
program Core;
procedure g (out r : int)
{
  r := 1;
};
procedure p (x : real, out y : int)
{
  if (real.gt(real.div(x, 0.0), 0.0)) { call g(out y); } else { y := 1; }
  assert [y_is_1]: y == 1;
};
#end

/-- info: symbolic: y_is_1 unknown
wp: y_is_1 unknown
symexec: y_is_1 unknown
per-path: y_is_1 unknown -/
#guard_msgs in
#eval printMarkerVerdicts divByZeroGuardPgm

/-- The call of `noPostcondCallPgm` to an abstract `g` without postconditions: every value of
    `y` after the call is a state of an execution, so `y_is_1` fails. -/
def abstractNoPostcondCallPgm :=
#strata
program Core;
procedure g (out r : int);
procedure p (x : int, out y : int)
{
  assert [x_pos]: int.gt(x, 0);
  call g(out y);
  assert [y_is_1]: y == 1;
};
#end

/-- info: symbolic: x_pos failed, y_is_1 failed
wp: x_pos failed, y_is_1 failed
symexec: x_pos failed, y_is_1 failed
per-path: x_pos failed, y_is_1 failed -/
#guard_msgs in
#eval printMarkerVerdicts abstractNoPostcondCallPgm

/-! An opaque callee (`Body.isOpaque`) is known to its callers only through its contract, which is
its call semantics, so a call to it carries no marker, with or without postconditions; its body is
still verified against its contract. Each callee below is checked in three kinds: transparent with
its body, opaque with the same body (`printOpaqueMarkerVerdicts`), and abstract. In every case
`y_is_1` has a counterexample in which the havocked output is not `1`: it is `unknown` after a
call to the transparent callee and `failed` after a call to the opaque or abstract one. -/

/-- info: symbolic: x_pos failed, y_is_1 failed
wp: x_pos failed, y_is_1 failed
symexec: x_pos failed, y_is_1 failed
per-path: x_pos failed, y_is_1 failed -/
#guard_msgs in
#eval printOpaqueMarkerVerdicts ["g"] noPostcondCallPgm

/-- The callee of `noPostcondCallPgm` with the postcondition `ensures true`. -/
def ensuresTrueCallPgm :=
#strata
program Core;
procedure g (out r : int)
spec { ensures true; }
{
  r := 1;
};
procedure p (x : int, out y : int)
{
  assert [x_pos]: int.gt(x, 0);
  call g(out y);
  assert [y_is_1]: y == 1;
};
#end

/-- info: symbolic: g_ensures_0 proved, x_pos failed, y_is_1 unknown
wp: g_ensures_0 proved, x_pos failed, y_is_1 unknown
symexec: g_ensures_0 proved, x_pos failed, y_is_1 unknown
per-path: g_ensures_0 proved, x_pos failed, y_is_1 unknown -/
#guard_msgs in
#eval printMarkerVerdicts ensuresTrueCallPgm

/-- info: symbolic: g_ensures_0 proved, x_pos failed, y_is_1 failed
wp: g_ensures_0 proved, x_pos failed, y_is_1 failed
symexec: g_ensures_0 proved, x_pos failed, y_is_1 failed
per-path: g_ensures_0 proved, x_pos failed, y_is_1 failed -/
#guard_msgs in
#eval printOpaqueMarkerVerdicts ["g"] ensuresTrueCallPgm

/-- The abstract callee of `ensuresTrueCallPgm`. -/
def abstractEnsuresTrueCallPgm :=
#strata
program Core;
procedure g (out r : int)
spec { ensures true; };
procedure p (x : int, out y : int)
{
  assert [x_pos]: int.gt(x, 0);
  call g(out y);
  assert [y_is_1]: y == 1;
};
#end

/-- info: symbolic: x_pos failed, y_is_1 failed
wp: x_pos failed, y_is_1 failed
symexec: x_pos failed, y_is_1 failed
per-path: x_pos failed, y_is_1 failed -/
#guard_msgs in
#eval printMarkerVerdicts abstractEnsuresTrueCallPgm

/-- The callee of `noPostcondCallPgm` with the postcondition `r ≥ 0`, which its body meets and
    which leaves `y = 0` possible after a call. -/
def realPostCallPgm :=
#strata
program Core;
procedure g (out r : int)
spec { ensures int.ge(r, 0); }
{
  r := 1;
};
procedure p (x : int, out y : int)
{
  assert [x_pos]: int.gt(x, 0);
  call g(out y);
  assert [y_is_1]: y == 1;
};
#end

/-- info: symbolic: g_ensures_0 proved, x_pos failed, y_is_1 unknown
wp: g_ensures_0 proved, x_pos failed, y_is_1 unknown
symexec: g_ensures_0 proved, x_pos failed, y_is_1 unknown
per-path: g_ensures_0 proved, x_pos failed, y_is_1 unknown -/
#guard_msgs in
#eval printMarkerVerdicts realPostCallPgm

/-- info: symbolic: g_ensures_0 proved, x_pos failed, y_is_1 failed
wp: g_ensures_0 proved, x_pos failed, y_is_1 failed
symexec: g_ensures_0 proved, x_pos failed, y_is_1 failed
per-path: g_ensures_0 proved, x_pos failed, y_is_1 failed -/
#guard_msgs in
#eval printOpaqueMarkerVerdicts ["g"] realPostCallPgm

/-- An opaque callee whose body violates its postcondition when `x < 0`: `g`'s own check
    `g_ensures_0` fails, so the flag does not skip the verification of its body, while the
    caller's `y_nonneg`, which follows from `g`'s contract, is proved. -/
def opaqueBadBodyPgm :=
#strata
program Core;
procedure g (x : int, out r : int)
spec { ensures int.ge(r, 0); }
{
  r := x;
};
procedure p (out y : int)
{
  call g(1, out y);
  assert [y_nonneg]: int.ge(y, 0);
};
#end

/-- info: symbolic: g_ensures_0 failed, y_nonneg proved
wp: g_ensures_0 failed, y_nonneg proved
symexec: g_ensures_0 failed, y_nonneg proved
per-path: g_ensures_0 failed, y_nonneg proved -/
#guard_msgs in
#eval printOpaqueMarkerVerdicts ["g"] opaqueBadBodyPgm

/-- `noPostcondCallPgm` with `g` written opaque in the surface syntax (`opaque` before its body). -/
def opaqueSyntaxPgm :=
#strata
program Core;
procedure g (out r : int)
opaque {
  r := 1;
};
procedure p (x : int, out y : int)
{
  assert [x_pos]: int.gt(x, 0);
  call g(out y);
  assert [y_is_1]: y == 1;
};
#end

/-- The verdicts of `program` in each of the `markerModes`, one line per mode. -/
def markerVerdictLines (program : Core.Program) : IO (List String) :=
  markerModes.mapM fun (mode, opts) => do
    let rs ← (Core.verifyProgram program opts).toIO IO.userError
    let vs := rs.toList.map fun r =>
      let v := if r.isSuccess then "proved" else if r.isFailure then "failed" else "unknown"
      s!"{r.obligation.label} {v}"
    pure s!"{mode}: {", ".intercalate vs}"

/-! The `opaque` mark survives printing and parsing again, and so do the verdicts: `y_is_1` fails
after the call to the opaque `g` both in the parsed program and in the program parsed back from
its printed text. -/

/-- info: printed g: procedure g (out r : int)
opaque {
  r := 1;
};
symbolic: x_pos failed, y_is_1 failed
wp: x_pos failed, y_is_1 failed
symexec: x_pos failed, y_is_1 failed
per-path: x_pos failed, y_is_1 failed
same verdicts after printing and parsing again: true -/
#guard_msgs in
#eval do
  let program ← IO.ofExcept (strataProgramToCore opaqueSyntaxPgm.program)
  let printed := (Core.formatProgram program).pretty
  let gText := (printed.splitOn "procedure g").getD 1 ""
  IO.println s!"printed g: procedure g{(gText.splitOn "procedure p").headD ""}".trimAsciiEnd
  let before ← markerVerdictLines program
  before.forM IO.println
  let reparsed ← IO.ofExcept (← Strata.Test.CoreReparse.parseAndTranslate printed)
  let after ← markerVerdictLines reparsed
  IO.println s!"same verdicts after printing and parsing again: {before == after}"

/-- The abstract callee of `realPostCallPgm`. -/
def abstractRealPostCallPgm :=
#strata
program Core;
procedure g (out r : int)
spec { ensures int.ge(r, 0); };
procedure p (x : int, out y : int)
{
  assert [x_pos]: int.gt(x, 0);
  call g(out y);
  assert [y_is_1]: y == 1;
};
#end

/-- info: symbolic: x_pos failed, y_is_1 failed
wp: x_pos failed, y_is_1 failed
symexec: x_pos failed, y_is_1 failed
per-path: x_pos failed, y_is_1 failed -/
#guard_msgs in
#eval printMarkerVerdicts abstractRealPostCallPgm

/-! The marker prefixes are reserved: each abstraction phase rejects a program with a label that
starts with its prefix (`Core.rejectMarkerLabels`), since a written assumption with such a label
would make its model check report a real failure after it as `unknown`. -/

/-- A written `assume` labelled with call elimination's prefix, before a failing assertion. -/
def userCallElimLabelPgm :=
#strata
program Core;
procedure P (x : int)
{
  assume [$__callElimAssume_user]: true;
  assert [x_pos]: int.gt(x, 0);
};
#end

/-- error: ❌ The label "$__callElimAssume_user" starts with "$__callElimAssume_", which call elimination reserves for its markers. -/
#guard_msgs in
#eval printMarkerVerdicts userCallElimLabelPgm

/-- A precondition labelled with the prefix of the insertion of loop invariant checks. -/
def userInvPrefixRequiresPgm :=
#strata
program Core;
procedure P (x : int)
spec { requires [$__insertLoopInvAssume_pre]: int.gt(x, 0); }
{
  assert [x_gt_1]: int.gt(x, 1);
};
#end

/-- error: ❌ The label "$__insertLoopInvAssume_pre" starts with "$__insertLoopInvAssume_", which the insertion of loop invariant checks reserves for its markers. -/
#guard_msgs in
#eval printMarkerVerdicts userInvPrefixRequiresPgm

/-- An axiom named with loop elimination's prefix. -/
def userLoopElimAxiomPgm :=
#strata
program Core;
axiom [$__loopElimAssume_ax]: true;
procedure P (x : int)
{
  assert [x_pos]: int.gt(x, 0);
};
#end

/-- error: ❌ The label "$__loopElimAssume_ax" starts with "$__loopElimAssume_", which loop elimination reserves for its markers. -/
#guard_msgs in
#eval printMarkerVerdicts userLoopElimAxiomPgm

/-- An `assume` in a block of a CFG body labelled with call elimination's prefix, rejected by the
    call-elimination phase (the verifier's pipeline stops earlier, at a CFG body). -/
def userCfgLabelPgm :=
#strata
program Core;
procedure P (x : int)
cfg entry {
  entry: {
    assume [$__callElimAssume_cfg]: true;
    assert [x_pos]: int.gt(x, 0);
    return;
  }
};
#end

/-- info: ❌ The label "$__callElimAssume_cfg" starts with "$__callElimAssume_", which call elimination reserves for its markers. -/
#guard_msgs in
#eval do
  let (p, _) := Strata.Core.getProgram userCfgLabelPgm Inhabited.default
  match _root_.Core.Transform.run p _root_.Core.callElimPipelinePhase.transform with
  | .error e => IO.println (toString (e.format none))
  | .ok _ => IO.println "accepted"

/-- A procedure whose name starts with the text of call elimination's marker prefix without its
    `$__`: its default postcondition label `callElimAssume_helper_ensures_0` is outside the reserved
    namespace, so the program is accepted and verified. -/
def helperNamePgm :=
#strata
program Core;
procedure callElimAssume_helper (x : int, out r : int)
spec { ensures r == x; }
{
  r := x;
};
procedure Main (x : int)
{
  assert [x_any]: int.ge(x, x);
};
#end

/-- info: symbolic: callElimAssume_helper_ensures_0 proved, x_any proved
wp: callElimAssume_helper_ensures_0 proved, x_any proved
symexec: callElimAssume_helper_ensures_0 proved, x_any proved
per-path: callElimAssume_helper_ensures_0 proved, x_any proved -/
#guard_msgs in
#eval printMarkerVerdicts helperNamePgm

/-- A loop invariant labelled with call elimination's prefix. -/
def userCallElimInvariantPgm :=
#strata
program Core;
procedure P (n : int)
{
  var i : int;
  i := 0;
  while (int.lt(i, n))
    invariant [$__callElimAssume_inv]: int.le(0, i)
  {
    i := int.add(i, 1);
  }
};
#end

/-- error: ❌ The label "$__callElimAssume_inv" starts with "$__callElimAssume_", which call elimination reserves for its markers. -/
#guard_msgs in
#eval printMarkerVerdicts userCallElimInvariantPgm

/-- A variable whose name starts with call elimination's marker prefix: a marker is an assumption,
    so the name of a variable declaration in the path condition is not read as one, and the
    failure of `x_pos` for `x + $__callElimAssume_t = 0` stays a failure in every mode. -/
def markerPrefixVarPgm :=
#strata
program Core;
procedure P (x : int)
{
  var $__callElimAssume_t : int := 0;
  havoc $__callElimAssume_t;
  assert [x_pos]: int.gt(int.add(x, $__callElimAssume_t), 0);
};
#end

/-- info: symbolic: x_pos failed
wp: x_pos failed
symexec: x_pos failed
per-path: x_pos failed -/
#guard_msgs in
#eval printMarkerVerdicts markerPrefixVarPgm

/-- An assertion on an input after a `while *` loop with an invariant: the invariant assumptions
    are on every path past the loop, the one that skips it included, so the failure is `unknown`
    in every mode. -/
def nondetInvariantPgm :=
#strata
program Core;
procedure P (x : int)
{
  var i : int;
  i := 0;
  while *
    invariant [i_nn]: int.ge(i, 0)
  {
    i := int.add(i, 1);
  }
  assert [x_pos]: int.gt(x, 0);
};
#end

/-- info: symbolic: insertLoopInvAssert_entry_invariant_loop_0_0_i_nn proved, insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0_i_nn proved, x_pos unknown
wp: insertLoopInvAssert_entry_invariant_loop_0_0_i_nn proved, insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0_i_nn proved, x_pos unknown
symexec: insertLoopInvAssert_entry_invariant_loop_0_0_i_nn proved, insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0_i_nn proved, x_pos unknown
per-path: insertLoopInvAssert_entry_invariant_loop_0_0_i_nn proved, insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0_i_nn proved, x_pos unknown -/
#guard_msgs in
#eval printMarkerVerdicts nondetInvariantPgm

/-- An assertion on an input after a `while *` loop with no invariant: the path that skips the loop
    carries no marker, so per-path symbolic execution reports the failure, while the modes that
    merge the paths before the assertion see the markers of the path through the arbitrary
    iteration. -/
def nondetNoInvariantPgm :=
#strata
program Core;
procedure P (x : int)
{
  var i : int;
  i := 0;
  while *
  {
    i := int.add(i, 1);
  }
  assert [x_pos]: int.gt(x, 0);
};
#end

/-- info: symbolic: x_pos unknown
wp: x_pos unknown
symexec: x_pos unknown
per-path: x_pos failed -/
#guard_msgs in
#eval printMarkerVerdicts nondetNoInvariantPgm

end Strata.LoopElimMarkerTest
