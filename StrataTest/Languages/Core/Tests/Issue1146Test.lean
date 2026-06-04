/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.DDMTransform.Translate
import StrataDDM.Integration.Lean.HashCommands

meta section

/-!
# Regression test for https://github.com/strata-org/Strata/issues/1146

A trailing `;` after a `function` body must not be silently accepted as an
empty `command_datatypes` block (which would later panic in
`translateDatatypes`), and a program mixing a datatype and a function must
translate cleanly.
-/

namespace Strata.Issue1146Test

/-! ## Canonical form: datatype + function translates without error -/

private def datatypeAndFunction : StrataDDM.Program :=
#strata
program Core;

datatype List () { Nil() };

function Len (xs : List) : int
{
  0
}
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram datatypeAndFunction) |>.snd |>.isEmpty

/-! ## Stray trailing `;` after a function body is a parse error -/

/--
error: unexpected token ';'; expected 'function', Core.Block or expected at least one element
-/
#guard_msgs in
def strayTrailingSemi : StrataDDM.Program :=
#strata
program Core;

datatype List () { Nil() };

function Len (xs : List) : int
{
  0
};
#end

end Strata.Issue1146Test

end
