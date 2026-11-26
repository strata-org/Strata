/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import Strata.Transform.CoreTypeCheck
import StrataDDM.Integration.Lean.HashCommands
import StrataTest.Languages.Core.Tests.TestUtil

/-! # The `$__` prefixes a program uses

The type-checking phase records the prefixes of the program's names in the `$__` namespace
(`Program.usedIdentPrefixes`), so that every such name starts with a recorded prefix. A program
that records nothing has its prefixes collected on demand (`Program.knownIdentPrefixes`). -/

namespace Strata.UsedIdentPrefixesTests

/-- Variables in the `$__` namespace: one followed by letters, one by a digit and one by an
    underscore. -/
def internalPgm :=
#strata
program Core;
procedure P (x : int)
{
  var $__ndelim_ite$_0 : int := x;
  var $__0 : int := x;
  var $___x : int := x;
  assert [a]: int.ge($__ndelim_ite$_0, int.add($__0, $___x));
};
#end

/-- The same program without them. -/
def plainPgm :=
#strata
program Core;
procedure P (x : int)
{
  assert [a]: int.ge(x, x);
};
#end

/-- The recorded prefixes after the type-checking phase (sorted), whether they cover the
    program's internal names, and whether each prefix of `pfxs` is free. -/
def run (p : Core.Program) (pfxs : List String) : IO Unit := do
  match ← (Core.runTransforms p [Core.typeCheckPipelinePhase .quiet]).toBaseIO with
  | .error e => IO.println e.message
  | .ok (p', _) =>
    IO.println s!"recorded: {p'.usedIdentPrefixes.map (·.mergeSort)}"
    IO.println s!"covered: {p'.identPrefixesCovered}"
    for pfx in pfxs do
      IO.println s!"free {pfx}: {p'.identPrefixesFree [pfx]}"

-- A digit or an underscore after `$__` is kept, so neither name records the bare `$__`, which
-- would overlap every prefix: `$__cse.` stays free.
/--
info: recorded: (some [$__0, $___, $__ndelim])
covered: true
free $__ndelim_ite$: false
free $__cse.: true
-/
#guard_msgs in
#eval run (Core.getProgram internalPgm).fst ["$__ndelim_ite$", "$__cse."]

-- A program without internal names records none, and every prefix is free.
/--
info: recorded: (some [])
covered: true
free $__ndelim_ite$: true
-/
#guard_msgs in
#eval run (Core.getProgram plainPgm).fst ["$__ndelim_ite$"]

-- A program that was not type checked records `none`; its prefixes are collected on demand, so
-- it is not taken as free of `$__ndelim`.
/--
info: recorded: none
known: [$__0, $___, $__ndelim]
free: false
-/
#guard_msgs in
#eval do
  let p := (Core.getProgram internalPgm).fst
  IO.println s!"recorded: {p.usedIdentPrefixes}"
  IO.println s!"known: {p.knownIdentPrefixes.mergeSort}"
  IO.println s!"free: {p.identPrefixesFree ["$__ndelim_ite$"]}"

end Strata.UsedIdentPrefixesTests
