/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section
---------------------------------------------------------------------
namespace Strata

def coverDiagnosticsPgm :=
#strata
program Core;
procedure Test()
{
  var x : int;
  assume (int.ge(x, 0));

  cover [unsatisfiable_cover]: int.lt(x, 0);
  assert [failing_assert]: int.lt(x, 0);
};
#end

/--
info: #["cover property is not satisfiable", "failing_assert does not hold"]
-/
#guard_msgs in
#eval do
  let results ← Core.verify coverDiagnosticsPgm (options := .quiet)
  let diagnostics := results.filterMap toDiagnosticModel
  return diagnostics.map DiagnosticModel.message

---------------------------------------------------------------------


-- Test that passing cover and assert produce no diagnostics
def passingPgm :=
#strata
program Core;
procedure Test()
{
  var x : int;
  assume (int.ge(x, 0));

  cover [satisfiable_cover]: int.ge(x, 0);
  assert [passing_assert]: int.ge(x, 0);
};
#end

/--
info: #[]
-/
#guard_msgs in
#eval do
  let results ← Core.verify passingPgm (options := .quiet)
  let diagnostics := results.filterMap toDiagnosticModel
  return diagnostics.map DiagnosticModel.message

---------------------------------------------------------------------


-- Test that satisfiable cover produces no diagnostic while unprovable assert does
def coverPassAssertFailPgm :=
#strata
program Core;
procedure Test()
{
  var x : int;

  cover [satisfiable_cover]: int.gt(x, 0);
  assert [unprovable_assert]: int.gt(x, 0);
};
#end

/--
info: #["unprovable_assert does not hold"]
-/
#guard_msgs in
#eval do
  let results ← Core.verify coverPassAssertFailPgm (options := .quiet)
  let diagnostics := results.filterMap toDiagnosticModel
  return diagnostics.map DiagnosticModel.message

end Strata
end
---------------------------------------------------------------------
