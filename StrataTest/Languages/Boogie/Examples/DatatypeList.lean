/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

/-!
# Recursive Datatype Example: IntList (Monomorphic)

This example demonstrates recursive datatypes with a concrete IntList type,
showing how to work with constructors, testers, and destructors
for recursive structures. Uses concrete types instead of polymorphism.
-/

def intListConsPgm : Program :=
#strata
program Boogie;

datatype IntList {
  Nil(),
  Cons(head: int, tail: IntList)
};

procedure testCons(x: int, xs: IntList) returns (r: IntList)
spec {
  ensures [r_is_cons]: (IntList..isCons(r));
  ensures [head_correct]: (IntList..head(r) == x);
  ensures [tail_correct]: (IntList..tail(r) == xs);
}
{
  r := Cons(x, xs);
  assert [r_is_cons]: IntList..isCons(r);
  assert [head_correct]: (IntList..head(r) == x);
  assert [tail_correct]: (IntList..tail(r) == xs);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram intListConsPgm) |>.snd |>.isEmpty

---------------------------------------------------------------------

def intListNilPgm : Program :=
#strata
program Boogie;

datatype IntList {
  Nil(),
  Cons(head: int, tail: IntList)
};

procedure testNil() returns (r: IntList)
spec {
  ensures [r_is_nil]: (IntList..isNil(r));
  ensures [r_not_cons]: (!IntList..isCons(r));
}
{
  r := Nil();
  assert [r_is_nil]: IntList..isNil(r);
  assert [r_not_cons]: !IntList..isCons(r);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram intListNilPgm) |>.snd |>.isEmpty

---------------------------------------------------------------------

def intListHeadPgm : Program :=
#strata
program Boogie;

datatype IntList {
  Nil(),
  Cons(head: int, tail: IntList)
};

procedure getHead(xs: IntList) returns (result: int)
spec {
  requires [xs_is_cons]: (IntList..isCons(xs));
  ensures [result_is_head]: (result == IntList..head(xs));
}
{
  assert [xs_is_cons]: IntList..isCons(xs);
  result := IntList..head(xs);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram intListHeadPgm) |>.snd |>.isEmpty

---------------------------------------------------------------------

def intListSingletonPgm : Program :=
#strata
program Boogie;

datatype IntList {
  Nil(),
  Cons(head: int, tail: IntList)
};

procedure singleton(x: int) returns (r: IntList)
spec {
  ensures [r_is_cons]: (IntList..isCons(r));
  ensures [head_is_x]: (IntList..head(r) == x);
  ensures [tail_is_nil]: (IntList..isNil(IntList..tail(r)));
}
{
  r := Cons(x, Nil());
  assert [r_is_cons]: IntList..isCons(r);
  assert [head_is_x]: (IntList..head(r) == x);
  assert [tail_is_nil]: IntList..isNil(IntList..tail(r));
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram intListSingletonPgm) |>.snd |>.isEmpty

---------------------------------------------------------------------

end Strata
