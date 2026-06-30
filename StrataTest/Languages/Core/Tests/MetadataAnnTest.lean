/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.DDMTransform.ASTtoCST
meta import Strata.Languages.Core.DDMTransform.Translate
meta import StrataDDM.Elab
meta import StrataDDM.BuiltinDialects.Init
import StrataDDM.Integration.Lean.HashCommands

meta section
open StrataDDM (Program initDialect)

/-!
# MetadataAnn Tests

Tests for the `@[key, key = value]` annotation grammar and the
`MetadataAnnFilter` that controls which metadata keys are emitted.
-/

namespace Strata.Test.MetadataAnn

open Strata
open Strata.CoreDDM
open Core

/-- Format a program with a given MetadataAnnFilter. -/
private def formatWithFilter (program : StrataDDM.Program) (filter : MetadataAnnFilter) : IO Unit := do
  let (ast, errs) := TransM.run Inhabited.default (translateProgram program)
  if !errs.isEmpty then
    IO.println s!"Translation errors: {errs}"
    return
  let formatted := (Core.formatProgram ast (annFilter := filter)).pretty
  IO.println formatted

-------------------------------------------------------------------------------
-- Test program with mixed annotations
-------------------------------------------------------------------------------

private def testPgm : Program :=
#strata
program Core;
procedure Test()
{
  var x : int;
  @[reachCheck] assert [a1]: (x > 0);
  @[reachCheck, propertyType = "divisionByZero"] assert [a2]: (x > 0);
  assert [a3]: (x > 0);
};
#end

-------------------------------------------------------------------------------
-- Filter = .none: no annotations emitted (default, preserves existing behavior)
-------------------------------------------------------------------------------

/--
info: program Core;

procedure Test ()
{
  var x : int;
  assert [a1]: x > 0;
  assert [a2]: x > 0;
  assert [a3]: x > 0;
};

-/
#guard_msgs in
#eval formatWithFilter testPgm .none

-------------------------------------------------------------------------------
-- Filter = .checks: only check flags emitted
-------------------------------------------------------------------------------

/--
info: program Core;

procedure Test ()
{
  var x : int;
  @[reachCheck] assert [a1]: x > 0;
  @[reachCheck] assert [a2]: x > 0;
  assert [a3]: x > 0;
};

-/
#guard_msgs in
#eval formatWithFilter testPgm .checks

-------------------------------------------------------------------------------
-- Filter = .properties: checks + propertyType/propertySummary
-------------------------------------------------------------------------------

/--
info: program Core;

procedure Test ()
{
  var x : int;
  @[reachCheck] assert [a1]: x > 0;
  @[reachCheck, propertyType = "divisionByZero"] assert [a2]: x > 0;
  assert [a3]: x > 0;
};

-/
#guard_msgs in
#eval formatWithFilter testPgm .properties

-------------------------------------------------------------------------------
-- Filter = .all: emits provenance (checked via IO, not #guard_msgs, since
-- byte offsets are fragile)
-------------------------------------------------------------------------------

private def hasSubstring (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- info: true -/
#guard_msgs in
#eval do
  let (ast, _) := TransM.run Inhabited.default (translateProgram testPgm)
  let formatted := (Core.formatProgram ast (annFilter := .all)).pretty
  return hasSubstring formatted "@[provenance" && hasSubstring formatted "reachCheck"

-------------------------------------------------------------------------------
-- Roundtrip: parse @[reachCheck] → translate → format with .checks → same text
-------------------------------------------------------------------------------

private def testRoundtrip : Program :=
#strata
program Core;
procedure Test()
{
  var x : int;
  @[reachCheck] assert [a1]: (x > 0);
  @[fullCheck] cover [c1]: (x > 0);
  @[customFlag, myTool = "info"] assert [a2]: (x > 0);
  assume [s1]: (x > 0);
};
#end

/--
info: program Core;

procedure Test ()
{
  var x : int;
  @[reachCheck] assert [a1]: x > 0;
  @[fullCheck] cover [c1]: x > 0;
  @[customFlag, myTool = "info"] assert [a2]: x > 0;
  assume [s1]: x > 0;
};

-/
#guard_msgs in
#eval formatWithFilter testRoundtrip (.allExcept (Std.HashSet.ofList ["provenance", "relatedFileRange"]))

end Strata.Test.MetadataAnn
