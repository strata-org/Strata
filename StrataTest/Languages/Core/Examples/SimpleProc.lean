/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def simpleProcPgm : Program :=
#strata
program Core;
procedure Test(x : bool, out y : bool)
spec {
  ensures (y == x);
  ensures (x == y);
}
{
  y := x || x;
};
#end

-- Translation from DDM AST to Strata Core AST

/--
info: true
-/
#guard_msgs in
-- No errors in translation.
#eval TransM.run Inhabited.default (translateProgram simpleProcPgm) |>.snd |>.isEmpty

/--
info: program Core;

procedure Test (x : bool, out y : bool)
spec {
  ensures [Test_ensures_0]: y == x;
  ensures [Test_ensures_1]: x == y;
  } {
  y := x || x;
};
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram simpleProcPgm) |>.fst

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: Test_ensures_0
Property: assert
Obligation:
(x@1 || x@1) == x@1

Label: Test_ensures_1
Property: assert
Obligation:
x@1 == (x@1 || x@1)

---
info:
Obligation: Test_ensures_0
Property: assert
Result: ✅ pass

Obligation: Test_ensures_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify simpleProcPgm

---------------------------------------------------------------------
