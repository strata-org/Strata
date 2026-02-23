/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# Polymorphic Datatype Integration Tests

Tests polymorphic datatype declarations in Core syntax, including function
generation (constructor, accessor, etc) and SMT verification for concrete
instantiations.
-/

namespace Strata.PolymorphicDatatypeTest

---------------------------------------------------------------------
-- Test 1: Option Datatype Declaration
---------------------------------------------------------------------

def optionDeclPgm : Program :=
#strata
program Core;

datatype Option (a : Type) { None(), Some(value: a) };

#end

/--
info: ok: datatype Option (a : Type) {(
  (None())),
  (Some(value : a))
};
-/
#guard_msgs in
#eval Core.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram optionDeclPgm)).fst

---------------------------------------------------------------------
-- Test 2: Option Used with Concrete Type (int)
---------------------------------------------------------------------

def optionIntPgm : Program :=
#strata
program Core;

datatype Option (a : Type) { None(), Some(value: a) };

procedure TestOptionInt() returns ()
spec {
  ensures true;
}
{
  var x : Option int;
  var y : Option int;
  var v : int;

  x := None();
  y := Some(42);
  v := Option..value(y);
  assert [valIs42]: v == 42;
};
#end

/--
info: ok: datatype Option (a : Type) {(
  (None())),
  (Some(value : a))
};
procedure TestOptionInt () returns ()
spec {
  ensures [TestOptionInt_ensures_0]: true;
  } {
  var x : (Option int);
  var y : (Option int);
  var v : int;
  x := None;
  y := Some(42);
  v := Option..value(y);
  assert [valIs42]: v == 42;
  };
-/
#guard_msgs in
#eval Core.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram optionIntPgm)).fst

---------------------------------------------------------------------
-- Test 3: List Used with Concrete Type (int)
---------------------------------------------------------------------

def listIntPgm : Program :=
#strata
program Core;

datatype List (a : Type) { Nil(), Cons(head: a, tail: List a) };

procedure TestListInt() returns ()
spec {
  ensures true;
}
{
  var xs : List int;
  var h : int;

  xs := Cons(1, Cons(2, Nil()));
  h := List..head(xs);
  assert [headIs1]: h == 1;
};
#end

/--
info: ok: datatype List (a : Type) {(
  (Nil())),
  (Cons(head : a, tail : (List a)))
};
procedure TestListInt () returns ()
spec {
  ensures [TestListInt_ensures_0]: true;
  } {
  var xs : (List int);
  var h : int;
  xs := Cons(1, Cons(2, Nil));
  h := List..head(xs);
  assert [headIs1]: h == 1;
  };
-/
#guard_msgs in
#eval Core.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram listIntPgm)).fst

---------------------------------------------------------------------
-- Test 4: Type with Multiple Parameters (Either)
---------------------------------------------------------------------

def eitherUsePgm : Program :=
#strata
program Core;

datatype Either (a : Type, b : Type) { Left(l: a), Right(r: b) };

procedure TestEither() returns ()
spec {
  ensures true;
}
{
  var x : Either int bool;
  var y : Either int bool;

  x := Left(42);
  y := Right(true);

  assert [xIsLeft]: Either..isLeft(x);
  assert [yIsRight]: Either..isRight(y);
  assert [lValue]: Either..l(x) == 42;
};
#end

/--
info: ok: datatype Either (a : Type, b : Type) {(
  (Left(l : a))),
  (Right(r : b))
};
procedure TestEither () returns ()
spec {
  ensures [TestEither_ensures_0]: true;
  } {
  var x : (Either int bool);
  var y : (Either int bool);
  x := Left(42);
  y := Right(true);
  assert [xIsLeft]: Either..isLeft(x);
  assert [yIsRight]: Either..isRight(y);
  assert [lValue]: Either..l(x) == 42;
  };
-/
#guard_msgs in
#eval Core.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram eitherUsePgm)).fst

---------------------------------------------------------------------
-- Test 5: Nested Polymorphic Types (Option of List)
---------------------------------------------------------------------

def nestedPolyPgm : Program :=
#strata
program Core;

datatype Option (a : Type) { None(), Some(value: a) };
datatype List (a : Type) { Nil(), Cons(head: a, tail: List a) };

procedure TestNestedPoly() returns ()
spec {
  ensures true;
}
{
  var x : Option (List int);

  x := Some(Cons(1, Nil()));
  assert [isSome]: Option..isSome(x);
};
#end

/--
info: ok: datatype Option (a : Type) {(
  (None())),
  (Some(value : a))
};
datatype List (a : Type) {(
  (Nil())),
  (Cons(head : a, tail : (List a)))
};
procedure TestNestedPoly () returns ()
spec {
  ensures [TestNestedPoly_ensures_0]: true;
  } {
  var x : (Option (List int));
  x := Some(Cons(1, Nil));
  assert [isSome]: Option..isSome(x);
  };
-/
#guard_msgs in
#eval Core.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram nestedPolyPgm)).fst

---------------------------------------------------------------------
-- Test 6: Polymorphic List Destructor with Havoc (SMT verification)
---------------------------------------------------------------------

def polyListHavocPgm : Program :=
#strata
program Core;

datatype List (a : Type) { Nil(), Cons(head: a, tail: List a) };

procedure TestPolyListHavoc() returns ()
spec {
  ensures true;
}
{
  var xs : List int;
  var h : int;

  xs := Nil();
  havoc xs;

  assume xs == Cons(100, Nil());

  h := List..head(xs);

  assert [headIs100]: h == 100;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram polyListHavocPgm) |>.snd |>.isEmpty

/--
info:
Obligation: headIs100
Property: assert
Result: ✅ pass

Obligation: TestPolyListHavoc_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify polyListHavocPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 7: Multiple Instantiations with SMT Verification
---------------------------------------------------------------------

/-- Test SMT verification with List int and List bool in same procedure -/
def multiInstSMTPgm : Program :=
#strata
program Core;

datatype List (a : Type) { Nil(), Cons(head: a, tail: List a) };

procedure TestMultiInstSMT() returns ()
spec {
  ensures true;
}
{
  var xs : List int;
  var ys : List bool;

  xs := Nil();
  ys := Nil();
  havoc xs;
  havoc ys;

  assume List..isCons(xs);
  assume List..isCons(ys);

  assert [bothCons]: List..isCons(xs) == List..isCons(ys);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram multiInstSMTPgm) |>.snd |>.isEmpty

/--
info:
Obligation: bothCons
Property: assert
Result: ✅ pass

Obligation: TestMultiInstSMT_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify multiInstSMTPgm (options := .quiet)


---------------------------------------------------------------------
-- Test 8: Multiple polymorphic arguments, constructor only needs 1
---------------------------------------------------------------------

def eitherHavocPgm : Program :=
#strata
program Core;

datatype Either (a : Type, b : Type) { Left(l: a), Right(r: b) };

procedure TestEitherHavoc() returns ()
spec {
  ensures true;
}
{
  var x : Either int bool;

  x := Left(0);
  havoc x;

  assume (x == Left(42));

  assert [isLeft]: Either..isLeft(x);
  assert [notRight]: !Either..isRight(x);
  assert [leftVal]: Either..l(x) == 42;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram eitherHavocPgm) |>.snd |>.isEmpty

/--
info:
Obligation: isLeft
Property: assert
Result: ✅ pass

Obligation: notRight
Property: assert
Result: ✅ pass

Obligation: leftVal
Property: assert
Result: ✅ pass

Obligation: TestEitherHavoc_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify eitherHavocPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 9: Polymorphic Precondition with Havoc
---------------------------------------------------------------------

def optionHavocPgm : Program :=
#strata
program Core;

datatype Option (a : Type) { None(), Some(value: a) };

function safeValue<a>(x : Option a) : a
  requires Option..isSome(x);
{ Option..value(x) }

procedure TestOptionHavoc() returns ()
spec {
  ensures true;
}
{
  var x : Option int;
  x := Some(42);
  havoc x;
  assume Option..isSome(x);
  var v : int;
  v := safeValue(x);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram optionHavocPgm) |>.snd |>.isEmpty

/--
info:
Obligation: set_v_calls_safeValue_0
Property: assert
Result: ✅ pass

Obligation: TestOptionHavoc_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify optionHavocPgm (options := .quiet)

end Strata.PolymorphicDatatypeTest
