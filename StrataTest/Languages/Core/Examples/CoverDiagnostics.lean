/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def coverDiagnosticsPgm :=
#strata
program Core;
procedure Test() returns ()
{
  var x : int;
  assume (x >= 0);

  cover [unsatisfiable_cover]: (x < 0);
  assert [failing_assert]: (x < 0);
};
#end

/--
info: #["cover property is not satisfiable", "assertion does not hold"]
-/
#guard_msgs in
#eval do
  let results ← verify "cvc5" coverDiagnosticsPgm (options := Options.quiet)
  let diagnostics := results.filterMap toDiagnosticModel
  return diagnostics.map DiagnosticModel.message

---------------------------------------------------------------------


-- Test that passing cover and assert produce no diagnostics
def passingPgm :=
#strata
program Core;
procedure Test() returns ()
{
  var x : int;
  assume (x >= 0);

  cover [satisfiable_cover]: (x >= 0);
  assert [passing_assert]: (x >= 0);
};
#end

/--
info: #[]
-/
#guard_msgs in
#eval do
  let results ← verify "cvc5" passingPgm (options := Options.quiet)
  let diagnostics := results.filterMap toDiagnosticModel
  return diagnostics.map DiagnosticModel.message

---------------------------------------------------------------------

-- Test diagnostic messages are different for cover vs assert
def mixedFailuresPgm :=
#strata
program Core;
procedure Test() returns ()
{
  var x : int;
  
  cover [cover_fail]: (false);
  assert [assert_fail]: (false);
};
#end

/--
info: #["cover property is not satisfiable", "assertion does not hold"]
-/
#guard_msgs in
#eval do
  let results ← verify "cvc5" mixedFailuresPgm (options := Options.quiet)
  let diagnostics := results.filterMap toDiagnosticModel
  return diagnostics.map DiagnosticModel.message

---------------------------------------------------------------------

---------------------------------------------------------------------
