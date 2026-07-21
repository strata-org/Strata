/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the `InlineLocalVariables` pass rewrites transparent (function)
bodies by inlining `var <name> := <expr>` declarations: every later reference
to `<name>` is replaced with the (already-inlined) initializer and the
declaration itself is dropped. Assignments to an inlined local are reported as
diagnostics.

The pass runs on the `$asFunction` copies produced by the transparency pass, but
it operates purely on a `Procedure`, so here we drive
`inlineLocalVariablesInFunction` directly on a parsed + resolved procedure and
compare its printed body against the expected output.
-/

import StrataTest.Util.TestLaurel
import Strata.Languages.Laurel.InlineLocalVariables
import Strata.Languages.Laurel.Resolution

open Strata
open StrataTest.Util

namespace Strata.Laurel

/-- Parse + resolve a program, then inline local variables in every procedure,
    printing each rewritten procedure and any diagnostics it produced. -/
private def printInlined (program : StrataDDM.Program) : IO Unit := do
  let laurelProgram ← translateLaurel program
  let resolved := (resolve laurelProgram).program
  for proc in resolved.staticProcedures do
    let (proc', diags) := inlineLocalVariablesInFunction proc
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc')))
    for d in diags do
      IO.println s!"diagnostic: {d.message}"

/-! ## A chain of `let`-style declarations is fully inlined -/

/--
info: procedure letChain()
  returns (r: int)
{
  return 0 + 1 + 1
};
-/
#guard_msgs in
#eval printInlined
#strata
program Laurel;
procedure letChain() returns (r: int) {
  var x: int := 0;
  var y: int := x + 1;
  var z: int := y + 1;
  return z
};
#end

/-! ## Only the declaration is dropped; other statements are kept and rewritten -/

/--
info: procedure keepsAssert()
  returns (r: int)
{
  assert 5 == 5;
  return 5
};
-/
#guard_msgs in
#eval printInlined
#strata
program Laurel;
procedure keepsAssert() returns (r: int) {
  var x: int := 5;
  assert x == 5;
  return x
};
#end

/-! ## Inlining duplicates the initializer at every reference

    A variable referenced more than once has its (whole) initializer expression
    copied to each use site — inlining is substitution, not sharing. -/

/--
info: procedure duplicates(a: int, b: int)
  returns (r: int)
{
  return (a + b) * (a + b)
};
-/
#guard_msgs in
#eval printInlined
#strata
program Laurel;
procedure duplicates(a: int, b: int) returns (r: int) {
  var x: int := a + b;
  return x * x
};
#end

/-! ## A quantifier's bound variable shadows an inlined local of the same name -/

/--
info: procedure shadowing()
  returns (r: bool)
{
  return forall(x: int) => x == x
};
-/
#guard_msgs in
#eval printInlined
#strata
program Laurel;
procedure shadowing() returns (r: bool) {
  var x: int := 7;
  return forall(x: int) => x == x
};
#end

end Laurel
