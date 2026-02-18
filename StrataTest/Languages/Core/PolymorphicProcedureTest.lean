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

/--
info: [Strata.Core] Type checking succeeded.


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


[DEBUG] Evaluated program:
datatype List (a : Type) {(
  (Nil())),
  (Cons(head : a, tail : (List a)))
};
procedure Extract (xs : (List $__ty0)) returns (h : ($__ty5))
spec {
  requires [Extract_requires_0]: List..isCons(xs);
  } {
  assume [Extract_requires_0]: List..isCons($__xs0);
  };
procedure Test () returns ()
spec {
  ensures [Test_ensures_0]: true;
  } {
  var xs : (List int);
  xs := Cons(1, Nil);
  havoc xs;
  var h : int;
  call h := Extract(xs);
  assert [Test_ensures_0]: true;
  };

---
info:
Obligation: (Origin_Extract_Requires)Extract_requires_0
Property: assert
Result: ❌ fail
Model:
($__xs2, (as Nil (List Int))

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify polyProcPgm

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
#eval verify polyPostPgm

end Strata.PolymorphicPostconditionTest
