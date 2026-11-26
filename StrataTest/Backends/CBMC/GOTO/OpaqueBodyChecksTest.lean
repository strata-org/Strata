/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Backends.CBMC.GOTO.CoreToGOTOPipeline
meta import StrataTest.Languages.Core.Tests.ReparseTestUtils

/-! # Opaque bodies in the GOTO export

`inlineCoreToGotoFiles` inlines an opaque callee as its contract, so it checks the callee's body
on its own in the GOTO `main`. A generic opaque body is checked once for each type at which it is
called: the generic `k`, called at `int`, is checked at `int`, so the GOTO program holds its
assertion `kbody`, which CBMC reports as a failure. -/

meta section

private def genericOpaquePgm : String :=
"program Core;

procedure k<a> (x : a)
opaque {
  assert [kbody]: false;
};
procedure main ()
{
  call k(0);
};
"

/-- The number of `ASSERT` instructions in the GOTO program that `inlineCoreToGotoFiles` writes
    for `text`, and whether one of them is labelled `label`. -/
private def gotoAsserts (text : String) (label : String) : IO (Nat × Bool) := do
  let p ← IO.ofExcept (← Strata.Test.CoreReparse.parseAndTranslate text)
  IO.FS.withTempDir fun dir => do
    let base := (dir / "out").toString
    match ← (Strata.inlineCoreToGotoFiles p base).toBaseIO with
    | .error e => throw (IO.userError e)
    | .ok () =>
      let g ← IO.FS.readFile s!"{base}.goto.json"
      return ((g.splitOn "\"ASSERT\"").length - 1, (g.splitOn label).length > 1)

-- The export prints the paths it writes, which name the temporary directory.
#guard_msgs (drop info) in
#eval do
  let r ← gotoAsserts genericOpaquePgm "kbody"
  unless r == (1, true) do throw (IO.userError s!"unexpected result {r}")

/-- A parameterless `main` with a contract is checked through a copy, like any other entry: the
    exported `main`, which also runs the check of the opaque `g`, carries no contract. -/
private def mainWithContractPgm : String :=
"program Core;

const c : int;

procedure g ()
opaque {
  assert [gbody]: false;
};
procedure main ()
spec {
  requires [mainpre]: c == 0;
} {
  call g();
};
"

/-- The symbol table that `inlineCoreToGotoFiles` writes for `text`. -/
private def gotoSymtab (text : String) : IO String := do
  let p ← IO.ofExcept (← Strata.Test.CoreReparse.parseAndTranslate text)
  IO.FS.withTempDir fun dir => do
    let base := (dir / "out").toString
    match ← (Strata.inlineCoreToGotoFiles p base).toBaseIO with
    | .error e => throw (IO.userError e)
    | .ok () => IO.FS.readFile s!"{base}.symtab.json"

#guard_msgs (drop info) in
#eval do
  let t ← gotoSymtab mainWithContractPgm
  if (t.splitOn "#spec_requires").length > 1 then
    throw (IO.userError "the exported main carries a contract")


/-- A transparent generic procedure whose recursive call is at a larger type (polymorphic
    recursion), with no opaque body anywhere: no body needs a per-instance check, so the export
    does not search the type instances, whose search would not terminate. The call to `c`, whose
    body is a CFG, then stops the export at inlining, before the recursion is inlined round
    after round; that error, not the instance search's, is the one the export reports. -/
private def polyRecursionPgm : String :=
"program Core;

procedure r<a> (x : a, b : bool)
{
  if (b) {
    var m : Map a int;
    call r(m, false);
  }
};
procedure c ()
cfg entry {
  entry: { return; }
};
procedure main ()
{
  call c();
  call r(1, true);
};
"

/-- info: runProgram: cannot apply statement-level transform to CFG body (procedure 'c') -/
#guard_msgs in
#eval do
  let p ← IO.ofExcept (← Strata.Test.CoreReparse.parseAndTranslate polyRecursionPgm)
  IO.FS.withTempDir fun dir => do
    match ← (Strata.inlineCoreToGotoFiles p (dir / "out").toString).toBaseIO with
    | .error e => IO.println e
    | .ok () => IO.println "exported"


/-- An opaque `c` whose body is a CFG, called from `main`: the export checks an opaque body
    through a copy inlined into structured code, which a CFG body cannot be, so it fails and
    names `c`, rather than leaving `c`'s postcondition unchecked. -/
private def opaqueCfgPgm : String :=
"program Core;

procedure c (out r : int)
spec {
  ensures [cpost]: r == 1;
} opaque cfg entry {
  entry: { r := 2; return; }
};
procedure main ()
{
  var x : int;
  call c(out x);
};
"

/-- info: GOTO export: procedure 'c' has a CFG body, which the export checks through a structured copy, so it cannot check that body -/
#guard_msgs in
#eval do
  let p ← IO.ofExcept (← Strata.Test.CoreReparse.parseAndTranslate opaqueCfgPgm)
  IO.FS.withTempDir fun dir => do
    match ← (Strata.inlineCoreToGotoFiles p (dir / "out").toString).toBaseIO with
    | .error e => IO.println e
    | .ok () => IO.println "exported"

/-- A parameterless entry named `__main__` that reaches no opaque body is exported as it is, as a
    parameterless `main` is: the GOTO program holds no check copy (`$checked`). -/
private def plainDunderMainPgm : String :=
"program Core;

procedure __main__ ()
{
  var x : int := 1;
  assert [xone]: x == 1;
};
"

#guard_msgs (drop info) in
#eval do
  let p ← IO.ofExcept (← Strata.Test.CoreReparse.parseAndTranslate plainDunderMainPgm)
  IO.FS.withTempDir fun dir => do
    let base := (dir / "out").toString
    match ← (Strata.inlineCoreToGotoFiles p base).toBaseIO with
    | .error e => throw (IO.userError e)
    | .ok () =>
      let g ← IO.FS.readFile s!"{base}.goto.json"
      let s ← IO.FS.readFile s!"{base}.symtab.json"
      unless (g.splitOn "$checked").length == 1 && (s.splitOn "$checked").length == 1 &&
          (g.splitOn "xone").length > 1 do
        throw (IO.userError "unexpected export of __main__")

/-- An opaque `g` whose body breaks its postcondition: the check of its body asserts the
    postcondition `gpost` after the body, so the GOTO program holds it (CBMC reports it as a
    failure), next to `main`'s own assertion. -/
private def brokenOpaquePostPgm : String :=
"program Core;

procedure g (out r : int)
spec {
  ensures [gpost]: r == 1;
} opaque {
  r := 2;
};
procedure main ()
{
  var x : int;
  call g(out x);
  assert [mainassert]: x == 1;
};
"

#guard_msgs (drop info) in
#eval do
  let r ← gotoAsserts brokenOpaquePostPgm "gpost"
  unless r == (2, true) do throw (IO.userError s!"unexpected result {r}")

end
