/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# Model Lifting Tests (SMT → LExpr)

Tests that models returned by the SMT solver are correctly
converted from `SMT.Term` to Core `LExpr` via `smtTermToLExpr` /
`convertModel`.  Each test defines a Strata Core program with a
deliberately failing assertion, runs `verify`, and checks the
`VCResult.lexprModel` field via `#guard_msgs` or `#eval` assertions.
-/

namespace Strata.ModelLiftTest
open Core Lambda

---------------------------------------------------------------------
-- Integer model
---------------------------------------------------------------------

def intModelPgm : Program :=
#strata
program Core;
procedure P() {
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
(x@1, 0)
-/
#guard_msgs in
#eval verify intModelPgm (options := .models)

-- The model value is an intConst
/--
info: failures=1 all_int=true
-/
#guard_msgs in
#eval do
  let results ← verify intModelPgm (options := .models)
  let failures := results.filter fun r => Core.VCResult.isFailure r
  let model : Core.LExprModel := match failures[0]? with
    | some r => r.lexprModel
    | none => []
  let allInt := model.all fun (_, expr) =>
    match expr with | .intConst _ _ => true | _ => false
  IO.println s!"failures={failures.size} all_int={allInt}"

---------------------------------------------------------------------
-- Boolean model
---------------------------------------------------------------------

def boolModelPgm : Program :=
#strata
program Core;
procedure P() {
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
(b@1, false)
-/
#guard_msgs in
#eval verify boolModelPgm (options := .models)

---------------------------------------------------------------------
-- Datatype model (Nil constructor)
---------------------------------------------------------------------

def datatypeModelPgm : Program :=
#strata
program Core;
datatype List (a : Type) { Nil(), Cons(head: a, tail: List a) };
procedure P() {
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
(xs@1, Nil)
-/
#guard_msgs in
#eval verify datatypeModelPgm (options := .models)

---------------------------------------------------------------------
-- Datatype model (Cons constructor)
---------------------------------------------------------------------

def datatypeModelPgm2 : Program :=
#strata
program Core;
datatype List (a : Type) { Nil(), Cons(head: a, tail: List a) };
procedure P() {
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
(xs@1, Cons(0, Nil))
-/
#guard_msgs in
#eval verify datatypeModelPgm2 (options := .models)

---------------------------------------------------------------------
-- Either datatype — model with algebraic type
---------------------------------------------------------------------

def eitherModelPgm : Program :=
#strata
program Core;
datatype Either (a : Type, b : Type) { Left(l: a), Right(r: b) };
procedure P() {
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
(e@1, Right(true))
-/
#guard_msgs in
#eval verify eitherModelPgm (options := .models)

---------------------------------------------------------------------
-- Quantifier model
--
-- `assert forall q : int :: q < x` always fails.
-- The model should contain an integer for x.
---------------------------------------------------------------------

def quantModelPgm : Program :=
#strata
program Core;
procedure P(x : int)
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
(x@1, 0)
-/
#guard_msgs in
#eval verify quantModelPgm (options := .models)

end Strata.ModelLiftTest
