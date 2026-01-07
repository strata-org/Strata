/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

/-!
# Polymorphic Datatype Integration Tests

Tests polymorphic datatype declarations in Boogie syntax. Verifies:
- Parsing of polymorphic datatype declarations with type parameters
- Constructor signatures have correct polymorphic types
- Tester functions have correct polymorphic signatures
- Accessor/destructor functions have correct polymorphic signatures
- Type checking succeeds with correct type parameter instantiation

Requirements: 2.1, 2.2, 2.3, 2.4, 2.5, 3.1, 3.3, 4.1, 4.2, 4.3, 4.4, 4.5
-/

namespace Strata.PolymorphicDatatypeTest

---------------------------------------------------------------------
-- Test 1: Option Datatype Declaration
---------------------------------------------------------------------

/-- Test that a polymorphic Option datatype can be declared -/
def optionDeclPgm : Program :=
#strata
program Boogie;

// Declare polymorphic Option datatype
datatype Option (a : Type) { None(), Some(value: a) };

#end

/-- info: ok: type:
Option
Type Arguments:
[a]
Constructors:
[Name: None Args: [] Tester: Option..isNone , Name: Some Args: [(value, a)] Tester: Option..isSome ]-/
#guard_msgs in
#eval Boogie.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram optionDeclPgm)).fst

---------------------------------------------------------------------
-- Test 2: Option Used with Concrete Type (int)
---------------------------------------------------------------------

/-- Test that Option can be instantiated with int -/
def optionIntPgm : Program :=
#strata
program Boogie;

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
  v := value(y);
  assert [valIs42]: v == 42;
};
#end

/-- info: ok: type:
Option
Type Arguments:
[a]
Constructors:
[Name: None Args: [] Tester: Option..isNone , Name: Some Args: [(value, a)] Tester: Option..isSome ]

(procedure TestOptionInt :  () → ())
modifies: []
preconditions: 
postconditions: (TestOptionInt_ensures_0, #true)
body: init (x : (Option int)) := (init_x_0 : (Option int))
init (y : (Option int)) := (init_y_1 : (Option int))
init (v : int) := (init_v_2 : int)
x := (~None : (Option int))
y := ((~Some : (arrow int (Option int))) #42)
v := ((~value : (arrow (Option int) int)) (y : (Option int)))
assert [valIs42] ((v : int) == #42)-/
#guard_msgs in
#eval Boogie.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram optionIntPgm)).fst

---------------------------------------------------------------------
-- Test 3: Option Used with Concrete Type (bool)
---------------------------------------------------------------------

/-- Test that Option can be instantiated with bool -/
def optionBoolPgm : Program :=
#strata
program Boogie;

datatype Option (a : Type) { None(), Some(value: a) };

procedure TestOptionBool() returns ()
spec {
  ensures true;
}
{
  var x : Option bool;
  x := Some(true);
  assert [isSome]: Option..isSome(x);
};
#end

/-- info: ok: type:
Option
Type Arguments:
[a]
Constructors:
[Name: None Args: [] Tester: Option..isNone , Name: Some Args: [(value, a)] Tester: Option..isSome ]

(procedure TestOptionBool :  () → ())
modifies: []
preconditions: 
postconditions: (TestOptionBool_ensures_0, #true)
body: init (x : (Option bool)) := (init_x_0 : (Option bool))
x := ((~Some : (arrow bool (Option bool))) #true)
assert [isSome] ((~Option..isSome : (arrow (Option bool) bool)) (x : (Option bool)))-/
#guard_msgs in
#eval Boogie.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram optionBoolPgm)).fst

---------------------------------------------------------------------
-- Test 4: List Datatype Declaration (Recursive)
---------------------------------------------------------------------

/-- Test that a polymorphic recursive List datatype can be declared -/
def listDeclPgm : Program :=
#strata
program Boogie;

// Declare polymorphic List datatype with recursive tail
datatype List (a : Type) { Nil(), Cons(head: a, tail: List a) };

#end

/-- info: ok: type:
List
Type Arguments:
[a]
Constructors:
[Name: Nil Args: [] Tester: List..isNil , Name: Cons Args: [(head, a), (tail, (List a))] Tester: List..isCons ]-/
#guard_msgs in
#eval Boogie.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram listDeclPgm)).fst

---------------------------------------------------------------------
-- Test 5: List Used with Concrete Type (int)
---------------------------------------------------------------------

/-- Test that List can be instantiated with int -/
def listIntPgm : Program :=
#strata
program Boogie;

datatype List (a : Type) { Nil(), Cons(head: a, tail: List a) };

procedure TestListInt() returns ()
spec {
  ensures true;
}
{
  var xs : List int;
  var h : int;

  xs := Cons(1, Cons(2, Nil()));
  h := head(xs);
  assert [headIs1]: h == 1;
};
#end

/-- info: ok: type:
List
Type Arguments:
[a]
Constructors:
[Name: Nil Args: [] Tester: List..isNil , Name: Cons Args: [(head, a), (tail, (List a))] Tester: List..isCons ]

(procedure TestListInt :  () → ())
modifies: []
preconditions: 
postconditions: (TestListInt_ensures_0, #true)
body: init (xs : (List int)) := (init_xs_0 : (List int))
init (h : int) := (init_h_1 : int)
xs := (((~Cons : (arrow int (arrow (List int) (List int)))) #1) (((~Cons : (arrow int (arrow (List int) (List int)))) #2) (~Nil : (List int))))
h := ((~head : (arrow (List int) int)) (xs : (List int)))
assert [headIs1] ((h : int) == #1)-/
#guard_msgs in
#eval Boogie.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram listIntPgm)).fst

---------------------------------------------------------------------
-- Test 6: List Tail Accessor
---------------------------------------------------------------------

/-- Test that tail accessor works correctly -/
def listTailPgm : Program :=
#strata
program Boogie;

datatype List (a : Type) { Nil(), Cons(head: a, tail: List a) };

procedure TestListTail() returns ()
spec {
  ensures true;
}
{
  var xs : List int;
  var ys : List int;

  xs := Cons(1, Cons(2, Nil()));
  ys := tail(xs);
  assert [tailHead]: head(ys) == 2;
};
#end

/-- info: ok: type:
List
Type Arguments:
[a]
Constructors:
[Name: Nil Args: [] Tester: List..isNil , Name: Cons Args: [(head, a), (tail, (List a))] Tester: List..isCons ]

(procedure TestListTail :  () → ())
modifies: []
preconditions: 
postconditions: (TestListTail_ensures_0, #true)
body: init (xs : (List int)) := (init_xs_0 : (List int))
init (ys : (List int)) := (init_ys_1 : (List int))
xs := (((~Cons : (arrow int (arrow (List int) (List int)))) #1) (((~Cons : (arrow int (arrow (List int) (List int)))) #2) (~Nil : (List int))))
ys := ((~tail : (arrow (List int) (List int))) (xs : (List int)))
assert [tailHead] (((~head : (arrow (List int) int)) (ys : (List int))) == #2)-/
#guard_msgs in
#eval Boogie.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram listTailPgm)).fst

---------------------------------------------------------------------
-- Test 7: Either Datatype (Multiple Type Parameters)
---------------------------------------------------------------------

/-- Test that a polymorphic Either datatype with two type parameters can be declared -/
def eitherDeclPgm : Program :=
#strata
program Boogie;

// Declare polymorphic Either datatype with two type parameters
datatype Either (a : Type, b : Type) { Left(l: a), Right(r: b) };

#end

/-- info: ok: type:
Either
Type Arguments:
[a, b]
Constructors:
[Name: Left Args: [(l, a)] Tester: Either..isLeft , Name: Right Args: [(r, b)] Tester: Either..isRight ]-/
#guard_msgs in
#eval Boogie.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram eitherDeclPgm)).fst

---------------------------------------------------------------------
-- Test 8: Either Used with Concrete Types
---------------------------------------------------------------------

/-- Test that Either can be instantiated with concrete types -/
def eitherUsePgm : Program :=
#strata
program Boogie;

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
  assert [lValue]: l(x) == 42;
};
#end

/-- info: ok: type:
Either
Type Arguments:
[a, b]
Constructors:
[Name: Left Args: [(l, a)] Tester: Either..isLeft , Name: Right Args: [(r, b)] Tester: Either..isRight ]

(procedure TestEither :  () → ())
modifies: []
preconditions: 
postconditions: (TestEither_ensures_0, #true)
body: init (x : (Either int bool)) := (init_x_0 : (Either int bool))
init (y : (Either int bool)) := (init_y_1 : (Either int bool))
x := ((~Left : (arrow int (Either int bool))) #42)
y := ((~Right : (arrow bool (Either int bool))) #true)
assert [xIsLeft] ((~Either..isLeft : (arrow (Either int bool) bool)) (x : (Either int bool)))
assert [yIsRight] ((~Either..isRight : (arrow (Either int bool) bool)) (y : (Either int bool)))
assert [lValue] (((~l : (arrow (Either int bool) int)) (x : (Either int bool))) == #42)-/
#guard_msgs in
#eval Boogie.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram eitherUsePgm)).fst

---------------------------------------------------------------------
-- Test 9: Nested Polymorphic Types (Option of List)
---------------------------------------------------------------------

/-- Test nested polymorphic types -/
def nestedPolyPgm : Program :=
#strata
program Boogie;

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

/-- info: ok: type:
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
preconditions: 
postconditions: (TestNestedPoly_ensures_0, #true)
body: init (x : (Option (List int))) := (init_x_0 : (Option (List int)))
x := ((~Some : (arrow (List int) (Option (List int)))) (((~Cons : (arrow int (arrow (List int) (List int)))) #1) (~Nil : (List int))))
assert [isSome] ((~Option..isSome : (arrow (Option (List int)) bool)) (x : (Option (List int))))-/
#guard_msgs in
#eval Boogie.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram nestedPolyPgm)).fst

---------------------------------------------------------------------
-- Test 10: Multiple Instantiations of Same Datatype in One Expression
---------------------------------------------------------------------

/-- Test using Option with different type parameters in same expression -/
def multiInstPgm : Program :=
#strata
program Boogie;

datatype Option (a : Type) { None(), Some(value: a) };

procedure TestMultiInst() returns ()
spec {
  ensures true;
}
{
  var x : Option int;
  var y : Option bool;

  x := Some(42);
  y := Some(true);

  assert [bothSome]: Option..isSome(x) == Option..isSome(y);
};
#end

/-- info: ok: type:
Option
Type Arguments:
[a]
Constructors:
[Name: None Args: [] Tester: Option..isNone , Name: Some Args: [(value, a)] Tester: Option..isSome ]

(procedure TestMultiInst :  () → ())
modifies: []
preconditions: 
postconditions: (TestMultiInst_ensures_0, #true)
body: init (x : (Option int)) := (init_x_0 : (Option int))
init (y : (Option bool)) := (init_y_1 : (Option bool))
x := ((~Some : (arrow int (Option int))) #42)
y := ((~Some : (arrow bool (Option bool))) #true)
assert [bothSome] (((~Option..isSome : (arrow (Option int) bool)) (x : (Option int))) == ((~Option..isSome : (arrow (Option bool) bool)) (y : (Option bool))))-/
#guard_msgs in
#eval Boogie.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram multiInstPgm)).fst

---------------------------------------------------------------------
-- Test 11: Polymorphic List Destructor with Havoc (SMT verification)
---------------------------------------------------------------------

/-- Test havoc with polymorphic List instantiated at int -/
def polyListHavocPgm : Program :=
#strata
program Boogie;

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

  h := head(xs);

  assert [headIs100]: h == 100;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram polyListHavocPgm) |>.snd |>.isEmpty

/--
info:
Obligation: headIs100
Result: verified

Obligation: TestPolyListHavoc_ensures_0
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" polyListHavocPgm Inhabited.default Options.quiet

---------------------------------------------------------------------
-- Test 12: Multiple Instantiations with SMT Verification
---------------------------------------------------------------------

/-- Test SMT verification with List int and List bool in same procedure -/
def multiInstSMTPgm : Program :=
#strata
program Boogie;

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
Result: verified

Obligation: TestMultiInstSMT_ensures_0
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" multiInstSMTPgm Inhabited.default Options.quiet

end Strata.PolymorphicDatatypeTest
