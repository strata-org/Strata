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

-------------------------------------------------------------------------------
-- Provenance string parsing: explicit provenance annotations are parsed back
-- to .provenance values, and round-trip through format. Note: provenance tags
-- are additive.
-------------------------------------------------------------------------------

private def testProvenanceParsing : Program :=
#strata
program Core;
procedure Test()
{
  var x : int;
  @[provenance = "myfile.st:100-200"] assert [a1]: (x > 0);
  @[provenance = "<synthesized:smt-encode>"] assert [a2]: (x > 0);
  @[provenance = "foo.st:10-20", relatedFileRange = "bar.st:30-40"] assert [a3]: (x > 0);
};
#end

/-- info: true -/
#guard_msgs in
#eval do
  let (ast, _) := TransM.run Inhabited.default (translateProgram testProvenanceParsing)
  let formatted := (Core.formatProgram ast (annFilter := .all)).pretty
  return hasSubstring formatted "myfile.st:100-200" &&
         hasSubstring formatted "<synthesized:smt-encode>" &&
         hasSubstring formatted "foo.st:10-20" &&
         hasSubstring formatted "bar.st:30-40"

-------------------------------------------------------------------------------
-- Annotations on various statement types (while, if, call, havoc, block, exit)
-------------------------------------------------------------------------------

private def testStmtVariety : Program :=
#strata
program Core;
procedure Callee (x : int)
{
  assume (x > 0);
};
procedure Test()
{
  var x : int;
  @[reachCheck] havoc x;
  @[fullCheck] x := 0;
  @[reachCheck] if (x > 0) {
    x := 1;
  } else {
    x := 2;
  }
  @[reachCheck] while (x > 0) {
    x := x + 1;
  }
  @[reachCheck] call Callee(x);
  @[reachCheck] blk: {
    x := 0;
  }
  @[reachCheck] exit blk;
};
#end

/--
info: program Core;

procedure Callee (x : int)
{
  assume [assume_0]: x > 0;
};
procedure Test ()
{
  var x : int;
  @[reachCheck] havoc x;
  @[fullCheck] x := 0;
  @[reachCheck] if (x > 0) {
    x := 1;
  } else {
    x := 2;
  }
  @[reachCheck] while (x > 0)
  {
    x := x + 1;
  }
  @[reachCheck] call Callee(x);
  @[reachCheck] blk: {
    x := 0;
  }
  @[reachCheck] exit blk;
};

-/
#guard_msgs in
#eval formatWithFilter testStmtVariety (.allExcept (Std.HashSet.ofList ["provenance", "relatedFileRange"]))

-------------------------------------------------------------------------------
-- Annotations on non-procedure commands (type, function, axiom, const, datatype)
-------------------------------------------------------------------------------

private def testCommandAnnotations : Program :=
#strata
program Core;

@[myTool = "generated"] type T0;
@[myTool = "generated"] type Alias := int;
@[myTool = "generated"] const c : int;
@[myTool = "generated"] function f (x : int) : int;
@[myTool = "generated"] function g (x : int) : int { x + 1 }
@[myTool = "generated"] axiom [ax1]: true;
@[myTool = "generated"] distinct [d1]: [c];
@[myTool = "generated"] datatype Color { Red(), Green(), Blue() };
#end

/--
info: program Core;

@[myTool = "generated"] type T0;
@[myTool = "generated"] type Alias := int;
@[myTool = "generated"] function c () : int;
@[myTool = "generated"] function f (x : int) : int;
@[myTool = "generated"] function g (x : int) : int {
  x + 1
}
@[myTool = "generated"] axiom [ax1]: true;
@[myTool = "generated"] distinct [d1]: [c];
@[myTool = "generated"] datatype Color {
  Red(),
  Green(),
  Blue()
};

-/
#guard_msgs in
#eval formatWithFilter testCommandAnnotations (.allExcept (Std.HashSet.ofList ["provenance", "relatedFileRange"]))

-------------------------------------------------------------------------------
-- Dialect-prefixed keys (opaque to Core, passed through)
-------------------------------------------------------------------------------

private def testDialectPrefixed : Program :=
#strata
program Core;
procedure Test()
{
  var x : int;
  @[python.source_line = "42", boogie.severity = "warning"] assert [a1]: (x > 0);
};
#end

/--
info: program Core;

procedure Test ()
{
  var x : int;
  @[python.source_line = "42", boogie.severity = "warning"] assert [a1]: x > 0;
};

-/
#guard_msgs in
#eval formatWithFilter testDialectPrefixed (.allExcept (Std.HashSet.ofList ["provenance", "relatedFileRange"]))

-------------------------------------------------------------------------------
-- Empty annotation @[] (edge case — no user-visible metadata emitted)
-------------------------------------------------------------------------------

private def testEmptyAnnotation : Program :=
#strata
program Core;
procedure Test()
{
  var x : int;
  @[] assert [a1]: (x > 0);
};
#end

/--
info: program Core;

procedure Test ()
{
  var x : int;
  assert [a1]: x > 0;
};

-/
#guard_msgs in
#eval formatWithFilter testEmptyAnnotation (.allExcept (Std.HashSet.ofList ["provenance", "relatedFileRange"]))

end Strata.Test.MetadataAnn
