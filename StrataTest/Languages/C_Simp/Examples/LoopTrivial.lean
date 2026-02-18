/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.C_Simp.C_Simp
import Strata.Languages.C_Simp.Verify

def LoopTrivialPgm :=
#strata
program C_Simp;

int procedure loopTrivial (n: int)
  //@pre (n >= 0);
  //@post true;
{
  var i : int;

  i = 0;
  while
  (i < n)
  //@decreases (n-i)
  //@invariant (i <= n)
  {
    i = i + 1;
  }

  //@assert [i_eq_n] (i == n);
  return i;
}

#end

/--
info: program C_Simp;
int procedure loopTrivial(n:int)//@pren>=(0);
//@posttrue;
  ({
  vari:int;
  i=0;
  while(i<n)
  //@decreases(n-i)//@invariant(i<=n)({
  i=i+(1);
  }
  )//@assert [i_eq_n]i==n;
  returni;
  }
  )
-/
#guard_msgs in
#eval IO.println LoopTrivialPgm

/--
info: function loopTrivial {
  pre: (~Int.Ge n #0)
  post: #true
  body:
{
  init (i : int) := init_i
  i := #0
  while
    (~Int.Lt i n)
    (some (~Int.Sub n i))
    (some (~Int.Le i n))
  {
    i := (~Int.Add i #1)
  }
  assert [i_eq_n] (i == n)
  return := i
}
}
Errors: #[]
-/
#guard_msgs in
open Strata.C_Simp in
#eval TransM.run (translateProgram (LoopTrivialPgm.commands))

/--
info: procedure loopTrivial (n : int) returns (return : int)
spec {
  requires [pre]: n >= 0;
  ensures [post]: true;
  } {
  var i : int;
  i := 0;
  if(i < n){
    first_iter_asserts: {
      assert [entry_invariant]: i <= n;
      assert [assert_measure_pos]: n - i >= 0;
      }|arbitrary iter facts|: {
      |loop havoc|: {
        havoc i;
        }arbitrary_iter_assumes: {
        assume [assume_guard]: i < n;
        assume [assume_invariant]: i <= n;
        assume [assume_measure_pos]: n - i >= 0;
        }var |special-name-for-old-measure-value| : int := n - i;
      i := i + 1;
      assert [measure_decreases]: n - i < special-name-for-old-measure-value;
      assert [measure_imp_not_guard]: if n - i <= 0 then !(i < n) else true;
      assert [arbitrary_iter_maintain_invariant]: i <= n;
      }|loop havoc|: {
      havoc i;
      }assume [not_guard]: !(i < n);
    assume [invariant]: i <= n;
    }assert [i_eq_n]: i == n;
  return := i;
  };
-/
#guard_msgs in
#eval Strata.to_core (Strata.C_Simp.get_program LoopTrivialPgm)

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: entry_invariant
Property: assert
Assumptions:
<label_ite_cond_true: (~Int.Lt i n)>: 0 < $__n0
pre: $__n0 >= 0
Obligation:
0 <= $__n0

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
assume_guard: $__i2 < $__n0
assume_invariant: $__i2 <= $__n0
assume_measure_pos: $__n0 - $__i2 >= 0
pre: $__n0 >= 0
Obligation:
$__n0 - ($__i2 + 1) < $__n0 - $__i2

Label: measure_imp_not_guard
Property: assert
Assumptions:
<label_ite_cond_true: (~Int.Lt i n)>: 0 < $__n0
assume_guard: $__i2 < $__n0
assume_invariant: $__i2 <= $__n0
assume_measure_pos: $__n0 - $__i2 >= 0
pre: $__n0 >= 0
Obligation:
if $__n0 - ($__i2 + 1) <= 0 then !($__i2 + 1 < $__n0) else true

Label: arbitrary_iter_maintain_invariant
Property: assert
Assumptions:
<label_ite_cond_true: (~Int.Lt i n)>: 0 < $__n0
assume_guard: $__i2 < $__n0
assume_invariant: $__i2 <= $__n0
assume_measure_pos: $__n0 - $__i2 >= 0
pre: $__n0 >= 0
Obligation:
$__i2 + 1 <= $__n0

Label: i_eq_n
Property: assert
Assumptions:
pre: $__n0 >= 0
<label_ite_cond_true: (~Int.Lt i n)>: if 0 < $__n0 then (0 < $__n0) else true
assume_guard: if 0 < $__n0 then ($__i2 < $__n0) else true
assume_invariant: if 0 < $__n0 then ($__i2 <= $__n0) else true
assume_measure_pos: if 0 < $__n0 then ($__n0 - $__i2 >= 0) else true
not_guard: if 0 < $__n0 then !($__i3 < $__n0) else true
invariant: if 0 < $__n0 then ($__i3 <= $__n0) else true
<label_ite_cond_false: !(~Int.Lt i n)>: if if 0 < $__n0 then false else true then if 0 < $__n0 then false else true else true
Obligation:
if 0 < $__n0 then $__i3 else 0 == $__n0

Label: post
Property: assert
Assumptions:
pre: $__n0 >= 0
<label_ite_cond_true: (~Int.Lt i n)>: if 0 < $__n0 then (0 < $__n0) else true
assume_guard: if 0 < $__n0 then ($__i2 < $__n0) else true
assume_invariant: if 0 < $__n0 then ($__i2 <= $__n0) else true
assume_measure_pos: if 0 < $__n0 then ($__n0 - $__i2 >= 0) else true
not_guard: if 0 < $__n0 then !($__i3 < $__n0) else true
invariant: if 0 < $__n0 then ($__i3 <= $__n0) else true
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

Obligation: i_eq_n
Property: assert
Result: ✅ pass

Obligation: post
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.C_Simp.verify LoopTrivialPgm
