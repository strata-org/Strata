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
  init (sum : int) := some init_sum
  init (i : int) := some init_i
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
info: procedure loopSimple :  ((n : int)) → ((return : int))
  modifies: []
  preconditions: (pre, (~Int.Ge n #0))
  postconditions: (post, #true)
{
  {
    init (sum : int) := some init_sum
    init (i : int) := some init_i
    sum := #0
    i := #0
    if (~Int.Lt i n) {
      first_iter_asserts :
      {
        assert [entry_invariant] (~Bool.And (~Int.Le i n) ((~Int.Div (~Int.Mul i (~Int.Sub i #1)) #2) == sum))
        assert [assert_measure_pos] (~Int.Ge (~Int.Sub n i) #0)
      }
      arbitrary iter facts :
      {
        loop havoc :
        {
          havoc sum
          havoc i
        }
        arbitrary_iter_assumes :
        {
          assume [assume_guard] (~Int.Lt i n)
          assume [assume_invariant] (~Bool.And (~Int.Le i n) ((~Int.Div (~Int.Mul i (~Int.Sub i #1)) #2) == sum))
          assume [assume_measure_pos] (~Int.Ge (~Int.Sub n i) #0)
        }
        init (special-name-for-old-measure-value : int) := some (~Int.Sub n i)
        sum := (~Int.Add sum i)
        i := (~Int.Add i #1)
        assert [measure_decreases] (~Int.Lt (~Int.Sub n i) special-name-for-old-measure-value)
        assert [measure_imp_not_guard] (if (~Int.Le (~Int.Sub n i) #0) then (~Bool.Not (~Int.Lt i n)) else #true)
        assert [arbitrary_iter_maintain_invariant] (~Bool.And
         (~Int.Le i n)
         ((~Int.Div (~Int.Mul i (~Int.Sub i #1)) #2) == sum))
      }
      loop havoc :
      {
        havoc sum
        havoc i
      }
      assume [not_guard] (~Bool.Not (~Int.Lt i n))
      assume [invariant] (~Bool.And (~Int.Le i n) ((~Int.Div (~Int.Mul i (~Int.Sub i #1)) #2) == sum))
    }
    else {}
    assert [sum_assert] ((~Int.Div (~Int.Mul n (~Int.Sub n #1)) #2) == sum)
    return := sum
  }
}
-/
#guard_msgs in
#eval Strata.to_core (Strata.C_Simp.get_program LoopSimplePgm)

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: entry_invariant
Property: assert
Assumptions:
(<label_ite_cond_true: (~Int.Lt i n)>, (~Int.Lt #0 $__n0))
(pre, (~Int.Ge $__n0 #0))

Proof Obligation:
(~Bool.And (~Int.Le #0 $__n0) #true)

Label: assert_measure_pos
Property: assert
Assumptions:
(<label_ite_cond_true: (~Int.Lt i n)>, (~Int.Lt #0 $__n0))
(pre, (~Int.Ge $__n0 #0))

Proof Obligation:
(~Int.Ge (~Int.Sub $__n0 #0) #0)

Label: measure_decreases
Property: assert
Assumptions:
(<label_ite_cond_true: (~Int.Lt i n)>, (~Int.Lt #0 $__n0))
(assume_guard, (~Int.Lt
 $__i3
 $__n0)) (assume_invariant, (~Bool.And
 (~Int.Le $__i3 $__n0)
 ((~Int.Div
   (~Int.Mul $__i3 (~Int.Sub $__i3 #1))
   #2) == $__sum2))) (assume_measure_pos, (~Int.Ge (~Int.Sub $__n0 $__i3) #0))
(pre, (~Int.Ge $__n0 #0))

Proof Obligation:
(~Int.Lt (~Int.Sub $__n0 (~Int.Add $__i3 #1)) (~Int.Sub $__n0 $__i3))

Label: measure_imp_not_guard
Property: assert
Assumptions:
(<label_ite_cond_true: (~Int.Lt i n)>, (~Int.Lt #0 $__n0))
(assume_guard, (~Int.Lt
 $__i3
 $__n0)) (assume_invariant, (~Bool.And
 (~Int.Le $__i3 $__n0)
 ((~Int.Div
   (~Int.Mul $__i3 (~Int.Sub $__i3 #1))
   #2) == $__sum2))) (assume_measure_pos, (~Int.Ge (~Int.Sub $__n0 $__i3) #0))
(pre, (~Int.Ge $__n0 #0))

Proof Obligation:
(if (~Int.Le (~Int.Sub $__n0 (~Int.Add $__i3 #1)) #0) then (~Bool.Not (~Int.Lt (~Int.Add $__i3 #1) $__n0)) else #true)

Label: arbitrary_iter_maintain_invariant
Property: assert
Assumptions:
(<label_ite_cond_true: (~Int.Lt i n)>, (~Int.Lt #0 $__n0))
(assume_guard, (~Int.Lt
 $__i3
 $__n0)) (assume_invariant, (~Bool.And
 (~Int.Le $__i3 $__n0)
 ((~Int.Div
   (~Int.Mul $__i3 (~Int.Sub $__i3 #1))
   #2) == $__sum2))) (assume_measure_pos, (~Int.Ge (~Int.Sub $__n0 $__i3) #0))
(pre, (~Int.Ge $__n0 #0))

Proof Obligation:
(~Bool.And
 (~Int.Le (~Int.Add $__i3 #1) $__n0)
 ((~Int.Div (~Int.Mul (~Int.Add $__i3 #1) (~Int.Sub (~Int.Add $__i3 #1) #1)) #2) == (~Int.Add $__sum2 $__i3)))

Label: sum_assert
Property: assert
Assumptions:
(pre, (~Int.Ge $__n0 #0))
(<label_ite_cond_true: (~Int.Lt i n)>, (if (~Int.Lt
  #0
  $__n0) then (~Int.Lt
  #0
  $__n0) else #true)) (assume_guard, (if (~Int.Lt
  #0
  $__n0) then (~Int.Lt
  $__i3
  $__n0) else #true)) (assume_invariant, (if (~Int.Lt
  #0
  $__n0) then (~Bool.And
  (~Int.Le $__i3 $__n0)
  ((~Int.Div
    (~Int.Mul $__i3 (~Int.Sub $__i3 #1))
    #2) == $__sum2)) else #true)) (assume_measure_pos, (if (~Int.Lt
  #0
  $__n0) then (~Int.Ge
  (~Int.Sub $__n0 $__i3)
  #0) else #true)) (not_guard, (if (~Int.Lt
  #0
  $__n0) then (~Bool.Not
  (~Int.Lt
   $__i5
   $__n0)) else #true)) (invariant, (if (~Int.Lt
  #0
  $__n0) then (~Bool.And
  (~Int.Le $__i5 $__n0)
  ((~Int.Div
    (~Int.Mul $__i5 (~Int.Sub $__i5 #1))
    #2) == $__sum4)) else #true)) (<label_ite_cond_false: !(~Int.Lt i n)>, (if (if (~Int.Lt
   #0
   $__n0) then #false else #true) then (if (~Int.Lt #0 $__n0) then #false else #true) else #true))

Proof Obligation:
((~Int.Div (~Int.Mul $__n0 (~Int.Sub $__n0 #1)) #2) == (if (~Int.Lt #0 $__n0) then $__sum4 else #0))

Label: post
Property: assert
Assumptions:
(pre, (~Int.Ge $__n0 #0))
(<label_ite_cond_true: (~Int.Lt i n)>, (if (~Int.Lt
  #0
  $__n0) then (~Int.Lt
  #0
  $__n0) else #true)) (assume_guard, (if (~Int.Lt
  #0
  $__n0) then (~Int.Lt
  $__i3
  $__n0) else #true)) (assume_invariant, (if (~Int.Lt
  #0
  $__n0) then (~Bool.And
  (~Int.Le $__i3 $__n0)
  ((~Int.Div
    (~Int.Mul $__i3 (~Int.Sub $__i3 #1))
    #2) == $__sum2)) else #true)) (assume_measure_pos, (if (~Int.Lt
  #0
  $__n0) then (~Int.Ge
  (~Int.Sub $__n0 $__i3)
  #0) else #true)) (not_guard, (if (~Int.Lt
  #0
  $__n0) then (~Bool.Not
  (~Int.Lt
   $__i5
   $__n0)) else #true)) (invariant, (if (~Int.Lt
  #0
  $__n0) then (~Bool.And
  (~Int.Le $__i5 $__n0)
  ((~Int.Div
    (~Int.Mul $__i5 (~Int.Sub $__i5 #1))
    #2) == $__sum4)) else #true)) (<label_ite_cond_false: !(~Int.Lt i n)>, (if (if (~Int.Lt
   #0
   $__n0) then #false else #true) then (if (~Int.Lt #0 $__n0) then #false else #true) else #true))

Proof Obligation:
#true



Obligation entry_invariant: SMT Solver Invocation Error!

Error: stderr:could not execute external process 'cvc5'
 
Ensure cvc5 is on your PATH or use --solver to specify another SMT solver.
solver stdout: t) := some init_i\n      sum := #0\n      i := #0\n      if (~Int.Lt i n) {\n        first_iter_asserts :\n        {\n          assert [entry_invariant] (~Bool.And (~Int.Le i n) ((~Int.Div (~Int.Mul i (~Int.Sub i #1)) #2) == sum))\n          assert [assert_measure_pos] (~Int.Ge (~Int.Sub n i) #0)\n        }\n        arbitrary iter facts :\n        {\n          loop havoc :\n          {\n            havoc sum\n            havoc i\n          }\n          arbitrary_iter_assumes :\n          {\n            assume [assume_guard] (~Int.Lt i n)\n            assume [assume_invariant] (~Bool.And (~Int.Le i n) ((~Int.Div (~Int.Mul i (~Int.Sub i #1)) #2) == sum))\n            assume [assume_measure_pos] (~Int.Ge (~Int.Sub n i) #0)\n          }\n-         init (special-name-for-old-measure-value : int) := (~Int.Sub n i)\n+         init (special-name-for-old-measure-value : int) := some (~Int.Sub n i)\n          sum := (~Int.Add sum i)\n          i := (~Int.Add i #1)\n          assert [measure_decreases] (~Int.Lt (~Int.Sub n i) special-name-for-old-measure-value)\n          assert [measure_imp_not_guard] (if (~Int.Le (~Int.Sub n i) #0) then (~Bool.Not (~Int.Lt i n)) else #true)\n          assert [arbitrary_iter_maintain_invariant] (~Bool.And\n           (~Int.Le i n)\n           ((~Int.Div (~Int.Mul i (~Int.Sub i #1)) #2) == sum))\n        }\n        loop havoc :\n        {\n          havoc sum\n          havoc i\n        }\n        assume [not_guard] (~Bool.Not (~Int.Lt i n))\n        assume [invariant] (~Bool.And (~Int.Le i n) ((~Int.Div (~Int.Mul i (~Int.Sub i #1)) #2) == sum))\n      }\n      else {}\n      assert [sum_assert] ((~Int.Div (~Int.Mul n (~Int.Sub n #1)) #2) == sum)\n      return := sum\n    }\n  }\n","endPos":{"column":11,"line":137},"fileName":"/local/home/mimayere/strata2/StrataTest/Languages/C_Simp/Examples/LoopSimple.lean","isSilent":false,"keepFullRange":false,"kind":"[anonymous]","pos":{"column":0,"line":137},"severity":"error"}



Evaluated program:
procedure loopSimple :  ((n : int)) → ((return : int))
  modifies: []
  preconditions: (pre, ((~Int.Ge : (arrow int (arrow int bool))) (n : int) #0))
  postconditions: (post, #true)
{
  {
    assume [pre] (~Int.Ge $__n0 #0)
    init (sum : int) := some init_sum
    init (i : int) := some init_i
    sum := #0
    i := #0
    if ((~Int.Lt : (arrow int (arrow int bool))) #0 ($__n0 : int)) {
      $_then :
      {
        first_iter_asserts :
        {
          assert [entry_invariant] (~Bool.And (~Int.Le #0 $__n0) #true)
          assert [assert_measure_pos] (~Int.Ge (~Int.Sub $__n0 #0) #0)
        }
        arbitrary iter facts :
        {
          loop havoc :
          {
            havoc sum
            havoc i
          }
          arbitrary_iter_assumes :
          {
            assume [assume_guard] (~Int.Lt $__i3 $__n0)
            assume [assume_invariant] (~Bool.And
             (~Int.Le $__i3 $__n0)
             ((~Int.Div (~Int.Mul $__i3 (~Int.Sub $__i3 #1)) #2) == $__sum2))
            assume [assume_measure_pos] (~Int.Ge (~Int.Sub $__n0 $__i3) #0)
          }
          init (special-name-for-old-measure-value : int) := some (~Int.Sub $__n0 $__i3)
          sum := (~Int.Add $__sum2 $__i3)
          i := (~Int.Add $__i3 #1)
          assert [measure_decreases] (~Int.Lt (~Int.Sub $__n0 (~Int.Add $__i3 #1)) (~Int.Sub $__n0 $__i3))
          assert [measure_imp_not_guard] (if (~Int.Le
            (~Int.Sub $__n0 (~Int.Add $__i3 #1))
            #0) then (~Bool.Not (~Int.Lt (~Int.Add $__i3 #1) $__n0)) else #true)
          assert [arbitrary_iter_maintain_invariant] (~Bool.And
           (~Int.Le (~Int.Add $__i3 #1) $__n0)
           ((~Int.Div (~Int.Mul (~Int.Add $__i3 #1) (~Int.Sub (~Int.Add $__i3 #1) #1)) #2) == (~Int.Add $__sum2 $__i3)))
        }
        loop havoc :
        {
          havoc sum
          havoc i
        }
        assume [not_guard] (~Bool.Not (~Int.Lt $__i5 $__n0))
        assume [invariant] (~Bool.And
         (~Int.Le $__i5 $__n0)
         ((~Int.Div (~Int.Mul $__i5 (~Int.Sub $__i5 #1)) #2) == $__sum4))
      }
    }
    else {
      $_else : {}
    }
    assert [sum_assert] ((~Int.Div
      (~Int.Mul $__n0 (~Int.Sub $__n0 #1))
      #2) == (if (~Int.Lt #0 $__n0) then $__sum4 else #0))
    return := (if (~Int.Lt #0 $__n0) then $__sum4 else #0)
    assert [post] #true
  }
}
---
-/
#guard_msgs in
#eval Strata.C_Simp.verify LoopSimplePgm
