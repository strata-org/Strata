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
procedure Extract<a>(xs : List a, out h : a)
spec {
  requires List..isCons(xs);
};
procedure Test() spec { ensures true; }
{
  var xs : List int;
  xs := Cons(1, Nil());
  havoc xs;
 //assume List..isCons(xs);
  var h : int;
  call Extract(xs, out h);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: callElimAssert_Extract_requires_0_2
Property: assert
Obligation:
List..isCons($__xs3)

Label: Test_ensures_0
Property: assert
Obligation:
true

---
info:
Obligation: callElimAssert_Extract_requires_0_2
Property: assert
Result: ❌ fail
Model:
($__xs3, Nil)

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
procedure MkCons<a>(x : a, out r : List a)
spec {
  free ensures List..isCons(r);
};
procedure Test() spec { ensures true; }
{
  var r : List int;
  call MkCons(1, out r);
  assert List..isCons(r);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: MkCons_ensures_0
Property: assert
Obligation:
true

Label: assert_0
Property: assert
Assumptions:
callElimAssume_MkCons_ensures_0_2: List..isCons($__r3)
Obligation:
List..isCons($__r3)

Label: Test_ensures_0
Property: assert
Assumptions:
callElimAssume_MkCons_ensures_0_2: List..isCons($__r3)
Obligation:
true

---
info:
Obligation: MkCons_ensures_0
Property: assert
Result: ✅ pass

Obligation: assert_0
Property: assert
Result: ✅ pass

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify polyPostPgm

end Strata.PolymorphicPostconditionTest
