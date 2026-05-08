/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Core
import Strata.Languages.Core.Verifier
import StrataTest.Languages.Core.Examples.Loops

---------------------------------------------------------------------
namespace Strata

def exitPgm : Program :=
#strata
program Core;
procedure Test1(x : bool, out y : bool)
{
    l1: {
      assert [a1]: x == x;
      exit l1;
      assert [a2]: !(x == x); // skipped because we exited l1
    }
    assert [a3]: x == x;
};

procedure Test2(x : int, out y : bool)
{
    l5: {
      l4: {
        l4_before: {
          l3_before: {
            l1: {
              assert [a4]: x == x;
              if (x > 0) {
                exit l3_before;
              } else {
                exit l4_before;
              }
            }
            l2: {
              assert [a5]: !(x == x); // skipped over
            }
          }
          assert [a6]: x * 2 > x;
          exit l5;
        }
        assert [a7]: x <= 0;
        exit l5;
      }
    }
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: a1
Property: assert
Obligation:
true

Label: a3
Property: assert
Obligation:
true

Label: a4
Property: assert
Obligation:
true

Label: a6
Property: assert
Assumptions:
<label_ite_cond_true: x > 0>: x@2 > 0
Obligation:
x@2 * 2 > x@2

Label: a7
Property: assert
Assumptions:
<label_ite_cond_false: !(x > 0)>: if x@2 > 0 then false else true
Obligation:
x@2 <= 0

---
info:
Obligation: a1
Property: assert
Result: ✅ pass

Obligation: a3
Property: assert
Result: ✅ pass

Obligation: a4
Property: assert
Result: ✅ pass

Obligation: a6
Property: assert
Result: ✅ pass

Obligation: a7
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify exitPgm


/--
info: Entry: l1

l1:
  #[<[fileRange]: :387-502>] condGoto true block$l1$_2 block$l1$_2
block$l1$_2:
  assert [a1]: x == x;
  #[<[fileRange]: :426-434>] condGoto true l$_1 l$_1
l$_1:
  assert [a3]: x == x;
  condGoto true end$_0 end$_0
end$_0:
  finish
-/
#guard_msgs in
#eval (Std.format (singleCFG exitPgm 0))

/--
info: Entry: l5

l5:
  #[<[fileRange]: :577-1056>] condGoto true l4 l4
l4:
  #[<[fileRange]: :589-1050>] condGoto true l4_before l4_before
l4_before:
  #[<[fileRange]: :603-996>] condGoto true l3_before l3_before
l3_before:
  #[<[fileRange]: :626-933>] condGoto true l1 l1
l1:
  #[<[fileRange]: :651-835>] condGoto true ite$_5 ite$_5
ite$_5:
  assert [a4]: x == x;
  #[<[fileRange]: :706-821>] condGoto x > 0 block$l5$_2 block$l5$_1
l2:
  #[<[fileRange]: :848-921>] condGoto true l$_3 l$_3
l$_3:
  assert [a5]: !(x == x);
  condGoto true block$l5$_2 block$l5$_2
block$l5$_2:
  assert [a6]: x * 2 > x;
  #[<[fileRange]: :978-986>] condGoto true end$_0 end$_0
block$l5$_1:
  assert [a7]: x <= 0;
  #[<[fileRange]: :1034-1042>] condGoto true end$_0 end$_0
end$_0:
  finish
-/
#guard_msgs in
#eval (Std.format (singleCFG exitPgm 1))
