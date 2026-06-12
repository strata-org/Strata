/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import StrataTest.Languages.Core.Examples.Loops
import StrataDDM.Integration.Lean.HashCommands

open StrataDDM (Program)
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
#eval Core.verify exitPgm


/--
info: Entry: block$l1$_2

l1:
  #[<[provenance]: :416-531>] condGoto true block$l1$_2 block$l1$_2
block$l1$_2:
  assert [a1]: x == x;
  #[<[provenance]: :455-463>] condGoto true l$_1 l$_1
l$_1:
  assert [a3]: x == x;
  #[<[provenance]: <synthesized:structured-to-unstructured>>] condGoto true end$_0 end$_0
end$_0:
  #[<[provenance]: <synthesized:structured-to-unstructured>>] finish
-/
#guard_msgs in
#eval (Std.format (singleCFG exitPgm 0))

/--
<<<<<<< HEAD
info: Entry: ite$_7

l5:
  #[<[provenance]: :606-1085>] condGoto true ite$_7 ite$_7
l4:
  #[<[provenance]: :618-1079>] condGoto true ite$_7 ite$_7
l4_before:
  #[<[provenance]: :632-1025>] condGoto true ite$_7 ite$_7
l3_before:
  #[<[provenance]: :655-962>] condGoto true ite$_7 ite$_7
=======
info: Entry: ite$_5

l5:
  condGoto true ite$_5 ite$_5
l4:
  condGoto true ite$_5 ite$_5
l4_before:
  condGoto true ite$_5 ite$_5
l3_before:
  condGoto true ite$_5 ite$_5
>>>>>>> origin/main2
l1:
  #[<[provenance]: :680-864>] condGoto true ite$_7 ite$_7
ite$_7:
  assert [a4]: x == x;
  #[<[provenance]: :735-850>] condGoto x > 0 block$l3_before$_5 block$l4_before$_6
block$l3_before$_5:
  #[<[provenance]: :764-779>] condGoto true block$l5$_2 block$l5$_2
block$l4_before$_6:
  #[<[provenance]: :819-834>] condGoto true block$l5$_1 block$l5$_1
l2:
  #[<[provenance]: :877-950>] condGoto true l$_3 l$_3
l$_3:
  assert [a5]: !(x == x);
  #[<[provenance]: <synthesized:structured-to-unstructured>>] condGoto true block$l5$_2 block$l5$_2
block$l5$_2:
  assert [a6]: x * 2 > x;
  #[<[provenance]: :1007-1015>] condGoto true end$_0 end$_0
block$l5$_1:
  assert [a7]: x <= 0;
  #[<[provenance]: :1063-1071>] condGoto true end$_0 end$_0
end$_0:
  #[<[provenance]: <synthesized:structured-to-unstructured>>] finish
-/
#guard_msgs in
#eval (Std.format (singleCFG exitPgm 1))
