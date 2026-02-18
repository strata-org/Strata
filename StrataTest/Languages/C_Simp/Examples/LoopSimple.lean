/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.C_Simp.C_Simp
import Strata.Languages.C_Simp.Verify

def LoopSimplePgm :=
#strata
program C_Simp;

int procedure loopSimple (n: int)
  //@pre (n >= 0);
  //@post true;
{
  var sum : int;
  var i : int;

  sum = 0;
  i = 0;
  while(i < n)
  //@decreases (n-i)
  //@invariant (i <= n && ((i * (i-1))/2 == sum))
  {
    sum = sum + i;
    i = i + 1;
  }
  //@assert [sum_assert] ((n * (n-1))/2 == sum);
  return sum;
}

#end

/--
info: program C_Simp;
int procedure loopSimple(n:int)//@pren>=(0);
//@posttrue;
  ({
  varsum:int;
  vari:int;
  sum=0;
  i=0;
  while(i<n)
  //@decreases(n-i)//@invariant((i<=n)&&(((i*(i-(1)))/(2))==sum))({
  sum=sum+i;
  i=i+(1);
  }
  )//@assert [sum_assert]((n*(n-(1)))/(2))==sum;
  returnsum;
  }
  )
-/
#guard_msgs in
#eval IO.println LoopSimplePgm

/--
info: function loopSimple {
  pre: (~Int.Ge n #0)
  post: #true
  body:
{
  init (sum : int) := init_sum
  init (i : int) := init_i
  sum := #0
  i := #0
  while
    (~Int.Lt i n)
    (some (~Int.Sub n i))
    (some (~Bool.And (~Int.Le i n) ((~Int.Div (~Int.Mul i (~Int.Sub i #1)) #2) == sum)))
  {
    sum := (~Int.Add sum i)
    i := (~Int.Add i #1)
  }
  assert [sum_assert] ((~Int.Div (~Int.Mul n (~Int.Sub n #1)) #2) == sum)
  return := sum
}
}
-/
#guard_msgs in
#eval Strata.C_Simp.get_program LoopSimplePgm

/--
info: procedure loopSimple (n : int) returns (return : int)
spec {
  requires [pre]: n >= 0;
  ensures [post]: true;
  } {
  var sum : int;
  var i : int;
  sum := 0;
  i := 0;
  if(i < n){
    first_iter_asserts: {
      assert [entry_invariant]: i <= n && i * (i - 1) div 2 == sum;
      assert [assert_measure_pos]: n - i >= 0;
      }|arbitrary iter facts|: {
      |loop havoc|: {
        havoc sum;
        havoc i;
        }arbitrary_iter_assumes: {
        assume [assume_guard]: i < n;
        assume [assume_invariant]: i <= n && i * (i - 1) div 2 == sum;
        assume [assume_measure_pos]: n - i >= 0;
        }var |special-name-for-old-measure-value| : int := n - i;
      sum := sum + i;
      i := i + 1;
      assert [measure_decreases]: n - i < special-name-for-old-measure-value;
      assert [measure_imp_not_guard]: if n - i <= 0 then !(i < n) else true;
      assert [arbitrary_iter_maintain_invariant]: i <= n && i * (i - 1) div 2 == sum;
      }|loop havoc|: {
      havoc sum;
      havoc i;
      }assume [not_guard]: !(i < n);
    assume [invariant]: i <= n && i * (i - 1) div 2 == sum;
    }assert [sum_assert]: n * (n - 1) div 2 == sum;
  return := sum;
  };
-/
#guard_msgs in
#eval Strata.to_core (Strata.C_Simp.get_program LoopSimplePgm)

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: entry_invariant
Property: assert
Assumptions:
<label_ite_cond_true: (~Int.Lt i n)>: 0 < $__n0
pre: $__n0 >= 0
Obligation:
0 <= $__n0 && true

Label: assert_measure_pos
Property: assert
Assumptions:
<label_ite_cond_true: (~Int.Lt i n)>: 0 < $__n0
pre: $__n0 >= 0
Obligation:
$__n0 - 0 >= 0

Label: measure_decreases
Property: assert
Assumptions:
<label_ite_cond_true: (~Int.Lt i n)>: 0 < $__n0
assume_guard: $__i3 < $__n0
assume_invariant: $__i3 <= $__n0 && $__i3 * ($__i3 - 1) div 2 == $__sum2
assume_measure_pos: $__n0 - $__i3 >= 0
pre: $__n0 >= 0
Obligation:
$__n0 - ($__i3 + 1) < $__n0 - $__i3

Label: measure_imp_not_guard
Property: assert
Assumptions:
<label_ite_cond_true: (~Int.Lt i n)>: 0 < $__n0
assume_guard: $__i3 < $__n0
assume_invariant: $__i3 <= $__n0 && $__i3 * ($__i3 - 1) div 2 == $__sum2
assume_measure_pos: $__n0 - $__i3 >= 0
pre: $__n0 >= 0
Obligation:
if $__n0 - ($__i3 + 1) <= 0 then !($__i3 + 1 < $__n0) else true

Label: arbitrary_iter_maintain_invariant
Property: assert
Assumptions:
<label_ite_cond_true: (~Int.Lt i n)>: 0 < $__n0
assume_guard: $__i3 < $__n0
assume_invariant: $__i3 <= $__n0 && $__i3 * ($__i3 - 1) div 2 == $__sum2
assume_measure_pos: $__n0 - $__i3 >= 0
pre: $__n0 >= 0
Obligation:
$__i3 + 1 <= $__n0 && ($__i3 + 1) * ($__i3 + 1 - 1) div 2 == $__sum2 + $__i3

Label: sum_assert
Property: assert
Assumptions:
pre: $__n0 >= 0
<label_ite_cond_true: (~Int.Lt i n)>: if 0 < $__n0 then (0 < $__n0) else true
assume_guard: if 0 < $__n0 then ($__i3 < $__n0) else true
assume_invariant: if 0 < $__n0 then ($__i3 <= $__n0 && $__i3 * ($__i3 - 1) div 2 == $__sum2) else true
assume_measure_pos: if 0 < $__n0 then ($__n0 - $__i3 >= 0) else true
not_guard: if 0 < $__n0 then !($__i5 < $__n0) else true
invariant: if 0 < $__n0 then ($__i5 <= $__n0 && $__i5 * ($__i5 - 1) div 2 == $__sum4) else true
<label_ite_cond_false: !(~Int.Lt i n)>: if if 0 < $__n0 then false else true then if 0 < $__n0 then false else true else true
Obligation:
$__n0 * ($__n0 - 1) div 2 == if 0 < $__n0 then $__sum4 else 0

Label: post
Property: assert
Assumptions:
pre: $__n0 >= 0
<label_ite_cond_true: (~Int.Lt i n)>: if 0 < $__n0 then (0 < $__n0) else true
assume_guard: if 0 < $__n0 then ($__i3 < $__n0) else true
assume_invariant: if 0 < $__n0 then ($__i3 <= $__n0 && $__i3 * ($__i3 - 1) div 2 == $__sum2) else true
assume_measure_pos: if 0 < $__n0 then ($__n0 - $__i3 >= 0) else true
not_guard: if 0 < $__n0 then !($__i5 < $__n0) else true
invariant: if 0 < $__n0 then ($__i5 <= $__n0 && $__i5 * ($__i5 - 1) div 2 == $__sum4) else true
<label_ite_cond_false: !(~Int.Lt i n)>: if if 0 < $__n0 then false else true then if 0 < $__n0 then false else true else true
Obligation:
true

---
info:
Obligation: entry_invariant
Property: assert
Result: ✅ pass

Obligation: assert_measure_pos
Property: assert
Result: ✅ pass

Obligation: measure_decreases
Property: assert
Result: ✅ pass

Obligation: measure_imp_not_guard
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant
Property: assert
Result: ✅ pass

Obligation: sum_assert
Property: assert
Result: ✅ pass

Obligation: post
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.C_Simp.verify LoopSimplePgm
