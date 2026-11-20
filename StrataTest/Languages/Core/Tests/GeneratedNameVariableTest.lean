/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

/-! # A variable named like a generated bound variable

The type checker names the variable it opens a quantifier with `$__var<n>`. A
program may declare a variable with such a name: the parser accepts it. The
type checker then picks a different name for the bound variable, so the program
type checks and the quantifier keeps its meaning: `d1_bad` compares every `x`
with the local `$__var0`, so it is refuted; `d1_ok` and `d2_ok` hold; and in
`d3_bad` the inner quantifier compares `y` with the local `$__var1`. -/

meta section

namespace Core.GeneratedNameVariableTest

private def pgm :=
#strata
program Core;
procedure P() {
  var $__var0 : int := 3;
  var $__var1 : int := 4;
  assert [d1_bad]: (forall x : int :: x == $__var0);
  assert [d1_ok]: (exists x : int :: x == $__var0);
  assume (exists x : int :: x != $__var0);
  assert [d2_ok]: (forall x : int :: x == x);
  assert [d3_bad]: (forall x : int :: forall y : int :: y == $__var1);
};
#end

/--
info: d1_bad: ❌ fail
d1_ok: ✅ pass
d2_ok: ✅ pass
d3_bad: ❌ fail
-/
#guard_msgs in
#eval do
  for r in ← Strata.Core.verify pgm (options := .quiet) do
    IO.println s!"{r.obligation.label}: {r.formatOutcome}"

end Core.GeneratedNameVariableTest

end
