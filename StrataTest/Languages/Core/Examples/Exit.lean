/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Languages.Core
meta import StrataTest.Languages.Core.Examples.Loops
import StrataDDM.Integration.Lean.HashCommands

meta section
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
  #[<[provenance]: :480-595>] condGoto true block$l1$_2 block$l1$_2
block$l1$_2:
  assert [a1]: x == x;
  #[<[provenance]: :519-527>] condGoto true l$_1 l$_1
l$_1:
  assert [a3]: x == x;
  condGoto true end$_0 end$_0
end$_0:
  #[<[provenance]: <synthesized:structured-to-unstructured>>] finish
-/
#guard_msgs in
#eval (Std.format (singleCFG exitPgm 0))

/--
info: Entry: ite$_7

l5:
  #[<[provenance]: :670-1149>] condGoto true ite$_7 ite$_7
l4:
  #[<[provenance]: :682-1143>] condGoto true ite$_7 ite$_7
l4_before:
  #[<[provenance]: :696-1089>] condGoto true ite$_7 ite$_7
l3_before:
  #[<[provenance]: :719-1026>] condGoto true ite$_7 ite$_7
l1:
  #[<[provenance]: :744-928>] condGoto true ite$_7 ite$_7
ite$_7:
  assert [a4]: x == x;
  #[<[provenance]: :799-914>] condGoto x > 0 block$l3_before$_5 block$l4_before$_6
block$l3_before$_5:
  #[<[provenance]: :828-843>] condGoto true block$l5$_2 block$l5$_2
block$l4_before$_6:
  #[<[provenance]: :883-898>] condGoto true block$l5$_1 block$l5$_1
l2:
  #[<[provenance]: :941-1014>] condGoto true l$_3 l$_3
l$_3:
  assert [a5]: !(x == x);
  condGoto true block$l5$_2 block$l5$_2
block$l5$_2:
  assert [a6]: x * 2 > x;
  #[<[provenance]: :1071-1079>] condGoto true end$_0 end$_0
block$l5$_1:
  assert [a7]: x <= 0;
  #[<[provenance]: :1127-1135>] condGoto true end$_0 end$_0
end$_0:
  #[<[provenance]: <synthesized:structured-to-unstructured>>] finish
-/
#guard_msgs in
#eval (Std.format (singleCFG exitPgm 1))

end Strata
end
