/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# Polymorphic Procedure Test
-/

namespace Strata.PolymorphicProcedureTest

---------------------------------------------------------------------
-- Test: Polymorphic procedure called at concrete type
---------------------------------------------------------------------

def polyProcPgm : Program :=
#strata
program Core;
datatype List (a : Type) { Nil(), Cons(head: a, tail: List a) };
procedure Extract<a>(xs : List a) returns (h : a)
spec {
  requires List..isCons(xs);
};
procedure Test() returns () spec { ensures true; }
{
  var xs : List int;
  xs := Cons(1, Nil());
  havoc xs;
 //assume List..isCons(xs);
  var h : int;
  call h := Extract(xs);
};
#end

/-- info: [Strata.Core] Type checking succeeded.


VCs:
Label: (Origin_Extract_Requires)Extract_requires_0
Property: assert
Assumptions:


Proof Obligation:
(~List..isCons $__xs2)

Label: Test_ensures_0
Property: assert
Assumptions:


Proof Obligation:
#true



Result: Obligation: (Origin_Extract_Requires)Extract_requires_0
Property: assert
Result: ❌ fail
Model:
($__xs2, (as Nil (List Int))


Evaluated program:
type:
List
Type Arguments:
[a]
Constructors:
[Name: Nil Args: [] Tester: List..isNil , Name: Cons Args: [(head, a), (tail, (List a))] Tester: List..isCons ]

procedure Extract :  ((xs : (List $__ty0))) → ((h : $__ty5))
  modifies: []
  preconditions: (Extract_requires_0, ((~List..isCons : (arrow (List $__ty0) bool)) (xs : (List $__ty0))))
  postconditions: 
{
  assume [Extract_requires_0] (~List..isCons $__xs0)
}
procedure Test :  () → ()
  modifies: []
  preconditions: 
  postconditions: (Test_ensures_0, #true)
{
  init (xs : (List int)) := init_xs_0
  xs := ((~Cons #1) ~Nil)
  havoc xs
  init (h : int) := init_h_1
  call [h] := Extract(xs)
  assert [Test_ensures_0] #true
}
---
info:
Obligation: (Origin_Extract_Requires)Extract_requires_0
Property: assert
Result: ❌ fail
Model:
($__xs2, (as Nil (List Int))

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval verify "cvc5" polyProcPgm

end Strata.PolymorphicProcedureTest

---------------------------------------------------------------------

namespace Strata.PolymorphicPostconditionTest

def polyPostPgm : Program :=
#strata
program Core;
datatype List (a : Type) { Nil(), Cons(head: a, tail: List a) };
procedure MkCons<a>(x : a) returns (r : List a)
spec {
  free ensures List..isCons(r);
};
procedure Test() returns () spec { ensures true; }
{
  var r : List int;
  call r := MkCons(1);
  assert List..isCons(r);
};
#end

/-- info: [Strata.Core] Type checking succeeded.


VCs:
Label: MkCons_ensures_0
Property: assert
Assumptions:


Proof Obligation:
#true

Label: assert_0
Property: assert
Assumptions:
((Origin_MkCons_Ensures)MkCons_ensures_0, (~List..isCons $__r2))

Proof Obligation:
(~List..isCons $__r2)

Label: Test_ensures_0
Property: assert
Assumptions:
((Origin_MkCons_Ensures)MkCons_ensures_0, (~List..isCons $__r2))

Proof Obligation:
#true

---
info: Obligation: MkCons_ensures_0
Property: assert
Result: ✅ pass

Obligation: assert_0
Property: assert
Result: ✅ pass

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval verify "cvc5" polyPostPgm 

end Strata.PolymorphicPostconditionTest
