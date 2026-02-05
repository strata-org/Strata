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

/-- info: ok: type:
Option
Type Arguments:
[a]
Constructors:
[Name: None Args: [] Tester: Option..isNone , Name: Some Args: [(value, a)] Tester: Option..isSome ]-/
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
info: ok: type:
Option
Type Arguments:
[a]
Constructors:
[Name: None Args: [] Tester: Option..isNone , Name: Some Args: [(value, a)] Tester: Option..isSome ]

(procedure TestOptionInt :  () → ())
modifies: []
preconditions: ⏎
postconditions: (TestOptionInt_ensures_0, #true)
body: init (x : (Option int)) := (init_x_0 : (Option int))
init (y : (Option int)) := (init_y_1 : (Option int))
init (v : int) := (init_v_2 : int)
x := (~None : (Option int))
y := ((~Some : (arrow int (Option int))) #42)
v := ((~Option..value : (arrow (Option int) int)) (y : (Option int)))
assert [valIs42] ((v : int) == #42)
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
info: ok: type:
List
Type Arguments:
[a]
Constructors:
[Name: Nil Args: [] Tester: List..isNil , Name: Cons Args: [(head, a), (tail, (List a))] Tester: List..isCons ]

(procedure TestListInt :  () → ())
modifies: []
preconditions: ⏎
postconditions: (TestListInt_ensures_0, #true)
body: init (xs : (List int)) := (init_xs_0 : (List int))
init (h : int) := (init_h_1 : int)
xs := (((~Cons : (arrow int (arrow (List int) (List int)))) #1) (((~Cons : (arrow int (arrow (List int) (List int)))) #2) (~Nil : (List int))))
h := ((~List..head : (arrow (List int) int)) (xs : (List int)))
assert [headIs1] ((h : int) == #1)
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
info: ok: type:
Either
Type Arguments:
[a, b]
Constructors:
[Name: Left Args: [(l, a)] Tester: Either..isLeft , Name: Right Args: [(r, b)] Tester: Either..isRight ]

(procedure TestEither :  () → ())
modifies: []
preconditions: ⏎
postconditions: (TestEither_ensures_0, #true)
body: init (x : (Either int bool)) := (init_x_0 : (Either int bool))
init (y : (Either int bool)) := (init_y_1 : (Either int bool))
x := ((~Left : (arrow int (Either int bool))) #42)
y := ((~Right : (arrow bool (Either int bool))) #true)
assert [xIsLeft] ((~Either..isLeft : (arrow (Either int bool) bool)) (x : (Either int bool)))
assert [yIsRight] ((~Either..isRight : (arrow (Either int bool) bool)) (y : (Either int bool)))
assert [lValue] (((~Either..l : (arrow (Either int bool) int)) (x : (Either int bool))) == #42)
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
info: ok: type:
Option
Type Arguments:
[a]
Constructors:
[Name: None Args: [] Tester: Option..isNone , Name: Some Args: [(value, a)] Tester: Option..isSome ]

type:
List
Type Arguments:
[a]
Constructors:
[Name: Nil Args: [] Tester: List..isNil , Name: Cons Args: [(head, a), (tail, (List a))] Tester: List..isCons ]

(procedure TestNestedPoly :  () → ())
modifies: []
preconditions: ⏎
postconditions: (TestNestedPoly_ensures_0, #true)
body: init (x : (Option (List int))) := (init_x_0 : (Option (List int)))
x := ((~Some : (arrow (List int) (Option (List int)))) (((~Cons : (arrow int (arrow (List int) (List int)))) #1) (~Nil : (List int))))
assert [isSome] ((~Option..isSome : (arrow (Option (List int)) bool)) (x : (Option (List int))))
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
#eval verify "cvc5" polyListHavocPgm (options := .quiet)

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
#eval verify "cvc5" multiInstSMTPgm (options := .quiet)


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
#eval verify "cvc5" eitherHavocPgm (options := .quiet)

end Strata.PolymorphicDatatypeTest
