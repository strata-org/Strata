/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# Datatype with Type Alias Test

Tests datatype declarations that use type aliases for constructor arguments.
Verifies that type aliases are correctly resolved in datatype field types.
-/

namespace Strata.DatatypeAliasTest

def datatypeAliasPgm : Program :=
#strata
program Core;

type MyInt := int;

datatype Box () { MkBox(value: MyInt) };

procedure TestBoxAlias() returns ()
spec {
  ensures true;
}
{
  var b : Box;
  var v : MyInt;

  b := MkBox(42);
  havoc b;
  assume b == MkBox(100);
  v := value(b);
  assert [valueIs100]: v == 100;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram datatypeAliasPgm) |>.snd |>.isEmpty

/--
info:
Obligation: valueIs100
Property: assert
Result: ✅ pass

Obligation: TestBoxAlias_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" datatypeAliasPgm Inhabited.default Options.quiet

end Strata.DatatypeAliasTest
