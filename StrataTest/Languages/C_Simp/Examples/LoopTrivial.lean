/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all Strata.Languages.C_Simp.C_Simp
meta import all Strata.Languages.C_Simp.Verify
import StrataDDM.Integration.Lean.HashCommands

meta section

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
int procedure loopTrivial(n:int)//@pre n>=0;
//@post true;
  ({
  vari:int;
  i=0;
  while(i<n)
  //@decreases (n-i)//@invariant (i<=n)({
  i=i+1;
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
  init (i : int)
  i := #0
  while
    (~Int.Lt i n)
    (some (~Int.Sub n i))
    [[loopTrivial_invariant_433_454]: (~Int.Le i n)]
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
#eval TransM.run Inhabited.default ((translateProgram (LoopTrivialPgm.commands)).map (·.stripMetaData))

/--
info: program Core;

procedure loopTrivial (n : int, out return : int)
spec {
  requires [pre]: int.ge(n, 0);
  ensures [post]: true;
  } {
  var i : int;
  i := 0;
  if (int.lt(i, n)) {
    first_iter_asserts: {
      assert [entry_invariant_0]: int.le(i, n);
      assert [assert_measure_pos]: int.ge(int.sub(n, i), 0);
    }
    |arbitrary iter facts|: {
      |loop havoc|: {
        havoc i;
      }
      arbitrary_iter_assumes: {
        assume [assume_guard]: int.lt(i, n);
        assume [assume_invariant_0]: int.le(i, n);
        assume [assume_measure_pos]: int.ge(int.sub(n, i), 0);
      }
      var |special-name-for-old-measure-value| : int := int.sub(n, i);
      i := int.add(i, 1);
      assert [measure_decreases]: int.lt(int.sub(n, i), special-name-for-old-measure-value);
      assert [measure_imp_not_guard]: if int.le(int.sub(n, i), 0) then !(int.lt(i, n)) else true;
      assert [arbitrary_iter_maintain_invariant_0]: int.le(i, n);
    }
    |loop havoc|: {
      havoc i;
    }
    assume [not_guard]: !(int.lt(i, n));
    assume [invariant_0]: int.le(i, n);
  }
  assert [i_eq_n]: i == n;
  return := i;
};
-/
#guard_msgs in
#eval Strata.to_core (Strata.C_Simp.get_program LoopTrivialPgm)

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: entry_invariant_0
Property: assert
Assumptions:
<label_ite_cond_true: int.lt(i, n)>: int.lt(0, n@1)
pre: int.ge(n@1, 0)
Obligation:
int.le(0, n@1)

Label: assert_measure_pos
Property: assert
Assumptions:
<label_ite_cond_true: int.lt(i, n)>: int.lt(0, n@1)
pre: int.ge(n@1, 0)
Obligation:
int.ge(int.sub(n@1, 0), 0)

Label: measure_decreases
Property: assert
Assumptions:
<label_ite_cond_true: int.lt(i, n)>: int.lt(0, n@1)
assume_guard: int.lt(i@1, n@1)
assume_invariant_0: int.le(i@1, n@1)
assume_measure_pos: int.ge(int.sub(n@1, i@1), 0)
pre: int.ge(n@1, 0)
Obligation:
int.lt(int.sub(n@1, int.add(i@1, 1)), int.sub(n@1, i@1))

Label: measure_imp_not_guard
Property: assert
Assumptions:
<label_ite_cond_true: int.lt(i, n)>: int.lt(0, n@1)
assume_guard: int.lt(i@1, n@1)
assume_invariant_0: int.le(i@1, n@1)
assume_measure_pos: int.ge(int.sub(n@1, i@1), 0)
pre: int.ge(n@1, 0)
Obligation:
if int.le(int.sub(n@1, int.add(i@1, 1)), 0) then !(int.lt(int.add(i@1, 1), n@1)) else true

Label: arbitrary_iter_maintain_invariant_0
Property: assert
Assumptions:
<label_ite_cond_true: int.lt(i, n)>: int.lt(0, n@1)
assume_guard: int.lt(i@1, n@1)
assume_invariant_0: int.le(i@1, n@1)
assume_measure_pos: int.ge(int.sub(n@1, i@1), 0)
pre: int.ge(n@1, 0)
Obligation:
int.le(int.add(i@1, 1), n@1)

Label: i_eq_n
Property: assert
Assumptions:
pre: int.ge(n@1, 0)
<label_ite_cond_true: int.lt(i, n)>: if int.lt(0, n@1) then int.lt(0, n@1) else true
assume_guard: if int.lt(0, n@1) then int.lt(i@1, n@1) else true
assume_invariant_0: if int.lt(0, n@1) then int.le(i@1, n@1) else true
assume_measure_pos: if int.lt(0, n@1) then int.ge(int.sub(n@1, i@1), 0) else true
not_guard: if int.lt(0, n@1) then !(int.lt(i@2, n@1)) else true
invariant_0: if int.lt(0, n@1) then int.le(i@2, n@1) else true
<label_ite_cond_false: !(int.lt(i, n))>: if if int.lt(0, n@1) then false else true then if int.lt(0, n@1) then false else true else true
Obligation:
(if int.lt(0, n@1) then i@2 else 0) == n@1

Label: post
Property: assert
Assumptions:
pre: int.ge(n@1, 0)
<label_ite_cond_true: int.lt(i, n)>: if int.lt(0, n@1) then int.lt(0, n@1) else true
assume_guard: if int.lt(0, n@1) then int.lt(i@1, n@1) else true
assume_invariant_0: if int.lt(0, n@1) then int.le(i@1, n@1) else true
assume_measure_pos: if int.lt(0, n@1) then int.ge(int.sub(n@1, i@1), 0) else true
not_guard: if int.lt(0, n@1) then !(int.lt(i@2, n@1)) else true
invariant_0: if int.lt(0, n@1) then int.le(i@2, n@1) else true
<label_ite_cond_false: !(int.lt(i, n))>: if if int.lt(0, n@1) then false else true then if int.lt(0, n@1) then false else true else true
Obligation:
true

---
info:
Obligation: entry_invariant_0
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

Obligation: arbitrary_iter_maintain_invariant_0
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

end
