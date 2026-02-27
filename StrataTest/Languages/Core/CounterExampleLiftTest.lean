/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# Counterexample Lifting Tests (SMT → LExpr)

Tests that counterexamples returned by the SMT solver are correctly
converted from `SMT.Term` to Core `LExpr` via `smtTermToLExpr` /
`convertCounterEx`.  Each test defines a Strata Core program with a
deliberately failing assertion, runs `verify`, and checks the
`VCResult.counterExample` field via `#guard_msgs` or `#eval` assertions.
-/

namespace Strata.CounterExampleLiftTest
open Core Lambda

---------------------------------------------------------------------
-- Integer counterexample
---------------------------------------------------------------------

def intCexPgm : Program :=
#strata
program Core;
procedure P() returns () {
  var x : int;
  havoc x;
  assert [must_be_42]: (x == 42);
};
#end

/--
info:
Obligation: must_be_42
Property: assert
Result: ❌ fail
Model:
($__x1, 0)
-/
#guard_msgs in
#eval verify intCexPgm (options := .models)

-- The counterexample value is an intConst
/-- info: failures=1 all_int=true -/
#guard_msgs in
#eval do
  let results ← verify intCexPgm (options := .models)
  let failures := results.filter fun r => Core.VCResult.isFailure r
  let cex : Core.LExprCounterEx := match failures[0]? with
    | some r => r.counterExample
    | none => []
  let allInt := cex.all fun (_, expr) =>
    match expr with | .intConst _ _ => true | _ => false
  IO.println s!"failures={failures.size} all_int={allInt}"

---------------------------------------------------------------------
-- Boolean counterexample
---------------------------------------------------------------------

def boolCexPgm : Program :=
#strata
program Core;
procedure P() returns () {
  var b : bool;
  havoc b;
  assert [must_be_true]: b;
};
#end

/--
info:
Obligation: must_be_true
Property: assert
Result: ❌ fail
Model:
($__b1, false)
-/
#guard_msgs in
#eval verify boolCexPgm (options := .models)

---------------------------------------------------------------------
-- Datatype counterexample (Nil constructor)
---------------------------------------------------------------------

def datatypeCexPgm : Program :=
#strata
program Core;
datatype List (a : Type) { Nil(), Cons(head: a, tail: List a) };
procedure P() returns () {
  var xs : List int;
  havoc xs;
  assert [must_be_cons]: List..isCons(xs);
};
#end

/--
info:
Obligation: must_be_cons
Property: assert
Result: ❌ fail
Model:
($__xs1, Nil)
-/
#guard_msgs in
#eval verify datatypeCexPgm (options := .models)

---------------------------------------------------------------------
-- Datatype counterexample (Cons constructor)
---------------------------------------------------------------------

def datatypeCexPgm2 : Program :=
#strata
program Core;
datatype List (a : Type) { Nil(), Cons(head: a, tail: List a) };
procedure P() returns () {
  var xs : List int;
  havoc xs;
  assert [must_be_cons]: List..isNil(xs);
};
#end

/--
info:
Obligation: must_be_cons
Property: assert
Result: ❌ fail
Model:
($__xs1, Cons(0, Nil))
-/
#guard_msgs in
#eval verify datatypeCexPgm2 (options := .models)

---------------------------------------------------------------------
-- Either datatype — counterexample with algebraic type
---------------------------------------------------------------------

def eitherCexPgm : Program :=
#strata
program Core;
datatype Either (a : Type, b : Type) { Left(l: a), Right(r: b) };
procedure P() returns () {
  var e : Either int bool;
  havoc e;
  assert [must_be_left]: Either..isLeft(e);
};
#end

/--
info:
Obligation: must_be_left
Property: assert
Result: ❌ fail
Model:
($__e1, Right(true))
-/
#guard_msgs in
#eval verify eitherCexPgm (options := .models)

---------------------------------------------------------------------
-- Quantifier counterexample
--
-- `assert forall q : int :: q < x` always fails.
-- The model should contain an integer for x.
---------------------------------------------------------------------

def quantCexPgm : Program :=
#strata
program Core;
procedure P(x : int) returns ()
spec {
  ensures [bad]: (forall q : int :: q < x);
}
{
};
#end

/--
info:
Obligation: bad
Property: assert
Result: ❌ fail
Model:
($__x0, 0)
-/
#guard_msgs in
#eval verify quantCexPgm (options := .models)

end Strata.CounterExampleLiftTest
