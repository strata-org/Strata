/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section
open StrataDDM (Program)

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
List..isCons(xs@2)

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
(xs@2, Nil)

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify polyProcPgm

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
Label: assert_0
Property: assert
Assumptions:
callElimPost_MkCons_ensures_0_2: List..isCons(r@2)
Obligation:
List..isCons(r@2)

Label: Test_ensures_0
Property: assert
Assumptions:
callElimPost_MkCons_ensures_0_2: List..isCons(r@2)
Obligation:
true

---
info:
Obligation: assert_0
Property: assert
Result: ✅ pass

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify polyPostPgm

end Strata.PolymorphicPostconditionTest

---------------------------------------------------------------------

namespace Strata.PolymorphicInoutPrecondTest

-- An in-out parameter's precondition constrains its type variable to a concrete
-- type, which is incompatible with the procedure being polymorphic. Type checking
-- treats `a` as a rigid type variable, and the precondition `x == 5` would refine it
-- to `int`, so the procedure is rejected.
def polyInoutPgm : Program :=
#strata
program Core;
procedure P<a>(inout x : a)
spec {
  requires (x == 5);
}
{
  x := true;
};
#end

/--
error: ❌ Type checking error.
Procedure 'P', condition 'P_requires_0': Rigid type variable 'a' was refined to 'int'
-/
#guard_msgs in
#eval Core.verify polyInoutPgm

end Strata.PolymorphicInoutPrecondTest

end
