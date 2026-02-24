/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def coverPgm1 :=
#strata
program Core;
procedure Test() returns ()
{
  var x : int;
  assume (x >= 0);

  if (false) {
    cover [unreachable_cover1]: (true);
    cover [unreachable_cover2]: (false);
    assert [unreachable_assert]: (false);
  } else {
    cover [reachable_cover]: (true);
    cover [unsatisfiable_cover]: (x == -1);
    assert [reachable_assert]: (true);
  }
};
#end


/--
info:
Obligation: unreachable_cover1
Property: cover
Result: ❌ fail

Obligation: unreachable_cover2
Property: cover
Result: ❌ fail

Obligation: unreachable_assert
Property: assert
Result: ✅ pass

Obligation: reachable_cover
Property: cover
Result: ✅ pass

Obligation: unsatisfiable_cover
Property: cover
Result: ❌ fail

Obligation: reachable_assert
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify coverPgm1 (options := Options.quiet)

---------------------------------------------------------------------

def coverPgm2 :=
#strata
program Core;
procedure Test(x : int) returns ()
spec {
  requires x > 1;
}
{
  if (x <= 1) {
    cover [ctest1]: (true);
  } else {
    cover [ctest2]: (x > 2);
    assert [atest2]: (x > 1);
  }
};
#end

/--
info:
Obligation: ctest1
Property: cover
Result: ❌ fail

Obligation: ctest2
Property: cover
Result: ✅ pass

Obligation: atest2
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify coverPgm2 (options := Options.quiet)

---------------------------------------------------------------------

-- Test: Global `reachCheck` with contradictory assumptions
--
-- Both assert and cover sit behind contradictory path conditions
-- (`x >= 0` ∧ `x < 0`). Without `reachCheck` they would be `pass`/`fail`
-- (vacuously); with `reachCheck` the unreachable diagnosis is set:
-- assertions on unreachable paths count as `pass` (vacuously true) and
-- covers on unreachable paths count as `fail`.
def reachCheckGlobalPgm :=
#strata
program Core;
procedure Test() returns ()
{
  var x : int;
  assume (x >= 0);
  assume (x < 0);

  assert [unreach_assert]: (x > 5);
  cover [unreach_cover]: (x > 5);
};
#end

/--
info:
Obligation: unreach_assert
Property: assert
Result: ✅ pass (❗path unreachable)

Obligation: unreach_cover
Property: cover
Result: ❌ fail (❗path unreachable)
-/
#guard_msgs in
#eval verify reachCheckGlobalPgm (options := {Options.quiet with reachCheck := true})

---------------------------------------------------------------------


-- Test: Global `reachCheck` with reachable and unreachable paths
--
-- The if-true branch is unreachable (`x >= 0` ∧ `x < 0`), while the
-- else branch is reachable. Obligations on the reachable path should
-- have their normal result; those on the unreachable path get the
-- unreachable diagnosis (assert → pass, cover → fail).
def reachCheckMixedPgm :=
#strata
program Core;
procedure Test() returns ()
{
  var x : int;
  assume (x >= 0);

  if (x < 0) {
    assert [unreach_assert]: (x == 42);
    cover [unreach_cover]: (x == 42);
  } else {
    assert [reach_assert_pass]: (x >= 0);
    cover [reach_cover_pass]: (x == 5);
    cover [reach_cover_fail]: (x < 0);
  }
};
#end

/--
info:
Obligation: unreach_assert
Property: assert
Result: ✅ pass (❗path unreachable)

Obligation: unreach_cover
Property: cover
Result: ❌ fail (❗path unreachable)

Obligation: reach_assert_pass
Property: assert
Result: ✅ pass

Obligation: reach_cover_pass
Property: cover
Result: ✅ pass

Obligation: reach_cover_fail
Property: cover
Result: ❌ fail
-/
#guard_msgs in
#eval verify reachCheckMixedPgm (options := {Options.quiet with reachCheck := true})

---------------------------------------------------------------------

-- Test: Per-statement `@[reachCheck]` annotation
--
-- Global `reachCheck` is off. Only statements with `@[reachCheck]` get
-- the reachability check. Non-annotated statements under the same
-- contradictory assumptions produce the old (vacuous) results.
-- Annotated statements on the unreachable path: assert → pass (with
-- unreachable diagnosis), cover → fail (with unreachable diagnosis).
def reachCheckPerStmtPgm :=
#strata
program Core;
procedure Test() returns ()
{
  var x : int;
  assume (x >= 0);
  assume (x < 0);

  @[reachCheck] assert [rc_assert]: (x > 5);
  assert [no_rc_assert]: (x > 5);
  @[reachCheck] cover [rc_cover]: (x > 5);
  cover [no_rc_cover]: (x > 5);
};
#end

/--
info:
Obligation: rc_assert
Property: assert
Result: ✅ pass (❗path unreachable)

Obligation: no_rc_assert
Property: assert
Result: ✅ pass

Obligation: rc_cover
Property: cover
Result: ❌ fail (❗path unreachable)

Obligation: no_rc_cover
Property: cover
Result: ❌ fail
-/
#guard_msgs in
#eval verify reachCheckPerStmtPgm (options := Options.quiet)

---------------------------------------------------------------------

-- Test: Diagnostic messages for unreachable outcomes
--
-- Verify that `toDiagnosticModel` produces the expected messages for
-- both assert and cover when they are unreachable.
def reachCheckDiagnosticsPgm :=
#strata
program Core;
procedure Test() returns ()
{
  var x : int;
  assume (x >= 0);
  assume (x < 0);

  assert [unreach_assert_diag]: (x > 5);
  cover [unreach_cover_diag]: (x > 5);
};
#end

/--
info: #["assertion holds vacuously (path unreachable)", "cover property is unreachable"]
-/
#guard_msgs in
#eval do
  let results ← verify reachCheckDiagnosticsPgm (options := {Options.quiet with reachCheck := true})
  let diagnostics := results.filterMap toDiagnosticModel
  return diagnostics.map DiagnosticModel.message

---------------------------------------------------------------------

-- Test: `reachCheck` overrides PE-optimized results
--
-- When `reachCheck` is active, even obligations that PE would normally
-- short-circuit (`assert(true)` → pass, `cover(false)` → fail) are sent
-- to the SMT solver so that the reachability check can detect unreachable
-- paths. Under contradictory assumptions (`x >= 0` ∧ `x < 0`), all four
-- obligations receive the unreachable diagnosis: assertions → pass,
-- covers → fail.
def reachCheckPEPgm :=
#strata
program Core;
procedure Test() returns ()
{
  var x : int;
  assume (x >= 0);
  assume (x < 0);

  assert [pe_assert_pass]: (true);
  cover [pe_cover_fail]: (false);
  assert [rc_assert]: (x > 5);
  cover [rc_cover]: (x > 5);
};
#end

/--
info:
Obligation: pe_assert_pass
Property: assert
Result: ✅ pass (❗path unreachable)

Obligation: pe_cover_fail
Property: cover
Result: ❌ fail (❗path unreachable)

Obligation: rc_assert
Property: assert
Result: ✅ pass (❗path unreachable)

Obligation: rc_cover
Property: cover
Result: ❌ fail (❗path unreachable)
-/
#guard_msgs in
#eval verify reachCheckPEPgm (options := {Options.quiet with reachCheck := true})

---------------------------------------------------------------------
