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
var g : bool;
procedure Test1(x : bool) returns (y : bool)
{
    l1: {
      assert [a1]: x == x;
      exit l1;
      assert [a2]: !(x == x); // skipped because we exited l1
    }
    assert [a3]: x == x;
};

procedure Test2(x : int) returns (y : bool)
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
<label_ite_cond_true: (~Int.Gt x #0)>: $__x3 > 0
Obligation:
$__x3 * 2 > $__x3

Label: a7
Property: assert
Assumptions:
<label_ite_cond_false: !(~Int.Gt x #0)>: if $__x3 > 0 then false else true
Obligation:
$__x3 <= 0

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

[l1:
   []
   cgoto #true block$l1$_2 block$l1$_2,
 block$l1$_2:
   [assert [a1] ((x : bool) == (x : bool))]
   cgoto #true l$_1 l$_1,
 l$_1:
   [assert [a3] ((x : bool) == (x : bool))]
   cgoto #true end$_0 end$_0,
 end$_0:
   []
   finish]
-/
#guard_msgs in
#eval (Std.format (singleCFG exitPgm 1))

/--
info: Entry: l5

[l5:
   []
   cgoto #true l4 l4,
 l4:
   []
   cgoto #true l4_before l4_before,
 l4_before:
   []
   cgoto #true l3_before l3_before,
 l3_before:
   []
   cgoto #true l1 l1,
 l1:
   []
   cgoto #true ite$_5 ite$_5,
 ite$_5:
   [assert [a4] ((x : int) == (x : int))]
   cgoto ((~Int.Gt : (arrow int (arrow int bool))) (x : int) #0) block$l5$_2 block$l5$_1,
 l2:
   []
   cgoto #true l$_3 l$_3,
 l$_3:
   [assert [a5] ((~Bool.Not : (arrow bool bool)) ((x : int) == (x : int)))]
   cgoto #true block$l5$_2 block$l5$_2,
 block$l5$_2:
   [assert [a6] ((~Int.Gt : (arrow int (arrow int bool)))
  ((~Int.Mul : (arrow int (arrow int int))) (x : int) #2)
  (x : int))]
   cgoto #true end$_0 end$_0,
 block$l5$_1:
   [assert [a7] ((~Int.Le : (arrow int (arrow int bool))) (x : int) #0)]
   cgoto #true end$_0 end$_0,
 end$_0:
   []
   finish]
-/
#guard_msgs in
#eval (Std.format (singleCFG exitPgm 2))
