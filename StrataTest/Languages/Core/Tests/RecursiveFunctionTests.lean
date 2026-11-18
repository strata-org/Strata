/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands
meta import StrataTest.Languages.Core.Tests.TestUtil

meta section
open StrataDDM (Program)

/-!
# Recursive Function Integration Tests

Tests recursive functions over algebraic datatypes using the `recursive function`
concrete syntax with `decreases` clauses. Verifies parsing, translation,
axiom-based SMT encoding, and end-to-end verification, then the type checker's
inferred measures and its requirements on recursive function blocks.
-/

namespace Strata.RecursiveFunctionTest

---------------------------------------------------------------------
-- Test 1: listLen — basic recursive function, ground assertions
---------------------------------------------------------------------

def listLenPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else int.add(1, listLen(IntList..tl(xs)))
};

procedure TestListLen()
spec {
  ensures true;
}
{
  assert [nilLen]: listLen(Nil()) == 0;
  assert [oneLen]: listLen(Cons(1, Nil())) == 1;
  assert [twoLen]: listLen(Cons(1, Cons(2, Nil()))) == 2;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram listLenPgm) |>.snd |>.isEmpty



/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: listLen_terminates_0
Property: assert
Obligation:
(forall x : IntList ::  { IntList..adtRank(x) }
  int.ge(IntList..adtRank(x), 0)) ==> (forall hd : int :: forall tl : IntList ::  { IntList..adtRank(Cons(hd, tl)) }
  int.lt(IntList..adtRank(tl), IntList..adtRank(Cons(hd, tl)))) ==> (forall x : IntList ::  { IntList..adtRank(x) }
  !(IntList..isNil(x)) ==> int.ge(IntList..adtRank(x), 1)) ==> !(IntList..isNil(xs@1)) ==> int.lt(IntList..adtRank(IntList..tl(xs@1)), IntList..adtRank(xs@1))

Label: listLen_body_calls_IntList..tl_0
Property: assert
Obligation:
!(IntList..isNil(xs@2)) ==> IntList..isCons(xs@2)

Label: nilLen
Property: assert
Obligation:
true

Label: oneLen
Property: assert
Obligation:
true

Label: twoLen
Property: assert
Obligation:
true

Label: TestListLen_ensures_0
Property: assert
Obligation:
true

---
info:
Obligation: listLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: listLen_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: nilLen
Property: assert
Result: ✅ pass

Obligation: oneLen
Property: assert
Result: ✅ pass

Obligation: twoLen
Property: assert
Result: ✅ pass

Obligation: TestListLen_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify listLenPgm (options := .default)

---------------------------------------------------------------------
-- Test 2: listLen with symbolic arguments and axiom reasoning
---------------------------------------------------------------------

def listLenAxiomPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else int.add(1, listLen(IntList..tl(xs)))
};

procedure TestNilCase(xs : IntList)
spec {
  requires IntList..isNil(xs);
  ensures true;
}
{
  assert [nilCase]: listLen(xs) == 0;
};

procedure TestConsCase(xs : IntList)
spec {
  requires IntList..isCons(xs);
  ensures true;
}
{
  assert [consLen]: listLen(xs) == int.add(1, listLen(IntList..tl(xs)));
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram listLenAxiomPgm) |>.snd |>.isEmpty

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: listLen_terminates_0
Property: assert
Obligation:
(forall x : IntList ::  { IntList..adtRank(x) }
  int.ge(IntList..adtRank(x), 0)) ==> (forall hd : int :: forall tl : IntList ::  { IntList..adtRank(Cons(hd, tl)) }
  int.lt(IntList..adtRank(tl), IntList..adtRank(Cons(hd, tl)))) ==> (forall x : IntList ::  { IntList..adtRank(x) }
  !(IntList..isNil(x)) ==> int.ge(IntList..adtRank(x), 1)) ==> !(IntList..isNil(xs@1)) ==> int.lt(IntList..adtRank(IntList..tl(xs@1)), IntList..adtRank(xs@1))

Label: listLen_body_calls_IntList..tl_0
Property: assert
Obligation:
!(IntList..isNil(xs@2)) ==> IntList..isCons(xs@2)

Label: nilCase
Property: assert
Assumptions:
TestNilCase_requires_0: IntList..isNil(xs@3)
Obligation:
listLen(xs@3) == 0

Label: TestNilCase_ensures_1
Property: assert
Assumptions:
TestNilCase_requires_0: IntList..isNil(xs@3)
Obligation:
true

Label: assert_consLen_calls_IntList..tl_0
Property: assert
Assumptions:
TestConsCase_requires_0: IntList..isCons(xs@4)
Obligation:
IntList..isCons(xs@4)

Label: consLen
Property: assert
Assumptions:
TestConsCase_requires_0: IntList..isCons(xs@4)
Obligation:
listLen(xs@4) == int.add(1, listLen(IntList..tl(xs@4)))

Label: TestConsCase_ensures_1
Property: assert
Assumptions:
TestConsCase_requires_0: IntList..isCons(xs@4)
Obligation:
true

---
info:
Obligation: listLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: listLen_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: nilCase
Property: assert
Result: ✅ pass

Obligation: TestNilCase_ensures_1
Property: assert
Result: ✅ pass

Obligation: assert_consLen_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: consLen
Property: assert
Result: ✅ pass

Obligation: TestConsCase_ensures_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify listLenAxiomPgm (options := .default)

---------------------------------------------------------------------
-- Test 3: recursive function with decreases on non-first parameter
---------------------------------------------------------------------

def lookupPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function contains (key : int, @[cases] xs : IntList) : bool
{
  if IntList..isNil(xs) then false
  else if IntList..hd(xs) == key then true
  else contains(key, IntList..tl(xs))
};

procedure TestContains()
spec {
  ensures true;
}
{
  assert [emptyList]: !contains(1, Nil());
  assert [found]: contains(2, Cons(1, Cons(2, Nil())));
  assert [notFound]: !contains(3, Cons(1, Cons(2, Nil())));
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram lookupPgm) |>.snd |>.isEmpty

/--
info:
Obligation: contains_terminates_0
Property: assert
Result: ✅ pass

Obligation: contains_body_calls_IntList..hd_0
Property: assert
Result: ✅ pass

Obligation: contains_body_calls_IntList..tl_1
Property: assert
Result: ✅ pass

Obligation: emptyList
Property: assert
Result: ✅ pass

Obligation: found
Property: assert
Result: ✅ pass

Obligation: notFound
Property: assert
Result: ✅ pass

Obligation: TestContains_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify lookupPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 4: imperative loop equivalent to recursive function
---------------------------------------------------------------------

def impEquivPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else int.add(1, listLen(IntList..tl(xs)))
};

procedure listLenImp(xs : IntList, out r : int)
spec {
  ensures [equiv]: r == listLen(xs);
}
{
  var cur : IntList;
  var acc : int;
  cur := xs;
  acc := 0;
  while (!IntList..isNil(cur))
    invariant int.add(acc, listLen(cur)) == listLen(xs)
    invariant int.ge(acc, 0)
  {
    acc := int.add(acc, 1);
    cur := IntList..tl(cur);
  }
  r := acc;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram impEquivPgm) |>.snd |>.isEmpty

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: listLen_terminates_0
Property: assert
Obligation:
(forall x : IntList ::  { IntList..adtRank(x) }
  int.ge(IntList..adtRank(x), 0)) ==> (forall hd : int :: forall tl : IntList ::  { IntList..adtRank(Cons(hd, tl)) }
  int.lt(IntList..adtRank(tl), IntList..adtRank(Cons(hd, tl)))) ==> (forall x : IntList ::  { IntList..adtRank(x) }
  !(IntList..isNil(x)) ==> int.ge(IntList..adtRank(x), 1)) ==> !(IntList..isNil(xs@1)) ==> int.lt(IntList..adtRank(IntList..tl(xs@1)), IntList..adtRank(xs@1))

Label: listLen_body_calls_IntList..tl_0
Property: assert
Obligation:
!(IntList..isNil(xs@2)) ==> IntList..isCons(xs@2)

Label: insertLoopInvAssert_entry_invariant_loop_0_0
Property: assert
Obligation:
int.add(0, listLen(xs@3)) == listLen(xs@3)

Label: insertLoopInvAssert_entry_invariant_loop_0_1
Property: assert
Obligation:
true

Label: set_cur_calls_IntList..tl_0
Property: assert
Assumptions:
<label_ite_cond_true: !(IntList..isNil(xs))>: !(IntList..isNil(xs@3))
$__loopElimAssume_guard_loop_1: !(IntList..isNil(cur@2))
insertLoopInvAssume_invariant_loop_0_0: int.add(acc@2, listLen(cur@2)) == listLen(xs@3)
insertLoopInvAssume_invariant_loop_0_1: int.ge(acc@2, 0)
insertLoopInvAssume_entry_invariant_loop_0_0: int.add(0, listLen(xs@3)) == listLen(xs@3)
Obligation:
IntList..isCons(cur@2)

Label: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0
Property: assert
Assumptions:
<label_ite_cond_true: !(IntList..isNil(xs))>: !(IntList..isNil(xs@3))
$__loopElimAssume_guard_loop_1: !(IntList..isNil(cur@2))
insertLoopInvAssume_invariant_loop_0_0: int.add(acc@2, listLen(cur@2)) == listLen(xs@3)
insertLoopInvAssume_invariant_loop_0_1: int.ge(acc@2, 0)
insertLoopInvAssume_entry_invariant_loop_0_0: int.add(0, listLen(xs@3)) == listLen(xs@3)
Obligation:
int.add(int.add(acc@2, 1), listLen(IntList..tl(cur@2))) == listLen(xs@3)

Label: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_1
Property: assert
Assumptions:
<label_ite_cond_true: !(IntList..isNil(xs))>: !(IntList..isNil(xs@3))
$__loopElimAssume_guard_loop_1: !(IntList..isNil(cur@2))
insertLoopInvAssume_invariant_loop_0_0: int.add(acc@2, listLen(cur@2)) == listLen(xs@3)
insertLoopInvAssume_invariant_loop_0_1: int.ge(acc@2, 0)
insertLoopInvAssume_entry_invariant_loop_0_0: int.add(0, listLen(xs@3)) == listLen(xs@3)
Obligation:
int.ge(int.add(acc@2, 1), 0)

Label: equiv
Property: assert
Assumptions:
insertLoopInvAssume_entry_invariant_loop_0_0: int.add(0, listLen(xs@3)) == listLen(xs@3)
<label_ite_cond_true: !(IntList..isNil(xs))>: if !(IntList..isNil(xs@3)) then !(IntList..isNil(xs@3)) else true
$__loopElimAssume_guard_loop_1: if !(IntList..isNil(xs@3)) then !(IntList..isNil(cur@2)) else true
insertLoopInvAssume_invariant_loop_0_0: if !(IntList..isNil(xs@3)) then int.add(acc@2, listLen(cur@2)) == listLen(xs@3) else true
insertLoopInvAssume_invariant_loop_0_1: if !(IntList..isNil(xs@3)) then int.ge(acc@2, 0) else true
$__loopElimAssume_not_guard_loop_1: if !(IntList..isNil(xs@3)) then !(!(IntList..isNil(cur@3))) else true
<label_ite_cond_false: !(!(IntList..isNil(xs)))>: if if !(IntList..isNil(xs@3)) then false else true then if !(IntList..isNil(xs@3)) then false else true else true
insertLoopInvAssume_exit_invariant_loop_0_0: int.add(if !(IntList..isNil(xs@3)) then acc@3 else 0, listLen(if !(IntList..isNil(xs@3)) then cur@3 else xs@3)) == listLen(xs@3)
insertLoopInvAssume_exit_invariant_loop_0_1: int.ge(if !(IntList..isNil(xs@3)) then acc@3 else 0, 0)
insertLoopInvAssume_exit_not_guard_loop_0: !(!(IntList..isNil(if !(IntList..isNil(xs@3)) then cur@3 else xs@3)))
Obligation:
(if !(IntList..isNil(xs@3)) then acc@3 else 0) == listLen(xs@3)

---
info:
Obligation: listLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: listLen_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_0_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_0_1
Property: assert
Result: ✅ pass

Obligation: set_cur_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_1
Property: assert
Result: ✅ pass

Obligation: equiv
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify impEquivPgm (options := .default)

---------------------------------------------------------------------
-- Test 5: recursive function with precondition
---------------------------------------------------------------------

def recPrecondPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else int.add(1, listLen(IntList..tl(xs)))
};

rec function nth (@[cases] xs : IntList, n : int) : int
  requires IntList..isCons(xs);
  requires int.ge(n, 0);
  requires int.lt(n, listLen(xs));
{
  if IntList..isNil(xs) then 0
  else if n == 0 then IntList..hd(xs)
  else nth(IntList..tl(xs), int.sub(n, 1))
};

procedure TestNth()
spec {
  ensures true;
}
{
  assert [first]:  nth(Cons(10, Cons(20, Nil())), 0) == 10;
  assert [second]: nth(Cons(10, Cons(20, Nil())), 1) == 20;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram recPrecondPgm) |>.snd |>.isEmpty

/--
info:
Obligation: listLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: listLen_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: nth_terminates_0
Property: assert
Result: ✅ pass

Obligation: nth_body_calls_IntList..hd_0
Property: assert
Result: ✅ pass

Obligation: nth_body_calls_IntList..tl_1
Property: assert
Result: ✅ pass

Obligation: nth_body_calls_nth_2
Property: assert
Result: ✅ pass

Obligation: nth_body_calls_nth_3
Property: assert
Result: ✅ pass

Obligation: nth_body_calls_nth_4
Property: assert
Result: ✅ pass

Obligation: assert_first_calls_nth_0
Property: assert
Result: ✅ pass

Obligation: assert_first_calls_nth_1
Property: assert
Result: ✅ pass

Obligation: assert_first_calls_nth_2
Property: assert
Result: ✅ pass

Obligation: first
Property: assert
Result: ✅ pass

Obligation: assert_second_calls_nth_0
Property: assert
Result: ✅ pass

Obligation: assert_second_calls_nth_1
Property: assert
Result: ✅ pass

Obligation: assert_second_calls_nth_2
Property: assert
Result: ✅ pass

Obligation: second
Property: assert
Result: ✅ pass

Obligation: TestNth_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify recPrecondPgm (options := .quiet)

---------------------------------------------------------------------
-- Test: an unused polymorphic recursive function is dropped
--
-- `len` is polymorphic and recursive but used at no ground type, so
-- `MonomorphizeFunctions` (which runs after type checking) drops its
-- *definition* as dead code before it can reach the SMT encoder.  Its body
-- well-formedness and termination lemmas are
-- emitted (at a fresh opaque type for the type variable) and pass.
---------------------------------------------------------------------

def polyRecPgm : Program :=
#strata
program Core;

datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };

rec function len<a>(@[cases] xs : MyList a) : int
{
  if MyList..isNil(xs) then 0 else int.add(1, len(MyList..tl(xs)))
};

#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram polyRecPgm) |>.snd |>.isEmpty

/--
info:
Obligation: len_terminates_0
Property: assert
Result: ✅ pass

Obligation: len_body_calls_MyList..tl_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify polyRecPgm (options := .quiet)

/-! ## Measures inferred from the integer requirement -/

/-- The measure the type checker stored for the recursive function `name`. -/
private def storedMeasure (p : Core.Program) (name : String) :
    Option Core.Expression.Expr :=
  p.decls.findSome? fun d =>
    match d with
    | .func f _ => if f.name.name == name then f.measure else none
    | .recFuncBlock fs _ => (fs.find? (·.name.name == name)).bind (·.measure)
    | _ => none

open Core.TestUtil (translateWithMetaData)

/-- The type-checked program, or `none` if type checking rejected it. -/
private def checked (p : StrataDDM.Program) : Option Core.Program :=
  (Core.typeCheck .quiet (translateWithMetaData p)).toOption

-- A measure `unconstrained()`, typed only by the requirement that measures be `int`, is accepted.
def measureSolvedByIntPgm : Program :=
#strata
program Core;

function unconstrained<a>() : a;

rec function countdown (n : int) : int
  decreases unconstrained()
{
  if int.le(n, 0) then 0 else countdown(int.sub(n, 1))
};
#end

/-- info: ok: program Core;

function unconstrained<a> () : a;
rec function countdown (n : int) : int
decreases unconstrained
  {
  if int.le(n, 0) then 0 else countdown(int.sub(n, 1))
};
-/
#guard_msgs (whitespace := lax) in
#eval Core.typeCheck .quiet (translateWithMetaData measureSolvedByIntPgm)

-- The stored measure records the inferred integer result type.
/--
info: some (LExpr.op () { name := "unconstrained", metadata := () } (some Lambda.LMonoTy.tcons "int" []))
-/
#guard_msgs (whitespace := lax) in
#eval repr (((checked measureSolvedByIntPgm).bind (storedMeasure · "countdown")).map
  Lambda.LExpr.eraseMetadata)

-- A concrete integer measure is accepted.
def measureIntExprPgm : Program :=
#strata
program Core;

rec function countdown (n : int) : int
  decreases int.add(n, 1)
{
  if int.le(n, 0) then 0 else countdown(int.sub(n, 1))
};
#end

/-- info: ok: program Core;

rec function countdown (n : int) : int
decreases int.add(n, 1)
  {
  if int.le(n, 0) then 0 else countdown(int.sub(n, 1))
};
-/
#guard_msgs (whitespace := lax) in
#eval Core.typeCheck .quiet (translateWithMetaData measureIntExprPgm)

end Strata.RecursiveFunctionTest

/-! ## Recursive function block type checking -/

namespace Core
section RecFuncBlock

open Lambda
open Std (Format ToFormat format)
open Core.TestUtil (programVerdict verdictOf xId)

/-- A non-recursive function record with a well-typed body. -/
private def plainMember : Function :=
  { name := ⟨"f", ()⟩, typeArgs := [],
    inputs := [(xId, LMonoTy.int)], output := LMonoTy.int,
    body := some (.fvar Core.coreLoc xId none) }

/-- A program containing exactly one recursive function block. -/
private def blockProgram (funcs : List Function) : Core.Program :=
  { decls := [.recFuncBlock funcs .empty] }

-- Repeated reserved member names are rejected as duplicate declarations.
private def duplicateReservedMember : Function :=
  { plainMember with name := ⟨"$__rigid_f", ()⟩, isRecursive := true }

/--
info: REJECTED: Error in recursive functions $__rigid_f: a declaration of this name already exists.
-/
#guard_msgs in
#eval programVerdict (blockProgram [duplicateReservedMember, duplicateReservedMember])

-- A block with no members is rejected.
/-- info: REJECTED: recursive function block must contain at least one function -/
#guard_msgs in
#eval verdictOf (RecFuncBlock.typeCheck initTyContext TEnv.default [])

/-! ## Every member carries the recursion flag -/

-- A member without the recursion flag is rejected.
/-- info: REJECTED: recursive function block member 'f' must be marked recursive -/
#guard_msgs in
#eval programVerdict (blockProgram [plainMember])

-- A flagged member need not call itself.
/-- info: ACCEPTED -/
#guard_msgs in
#eval programVerdict (blockProgram [{ plainMember with isRecursive := true }])

/-- A one-member block may call itself. -/
private def selfRecursiveMember : Function :=
  { name := ⟨"f", ()⟩, typeArgs := [], isRecursive := true,
    inputs := [(xId, LMonoTy.int)], output := LMonoTy.int,
    body := some (.app Core.coreLoc (.op Core.coreLoc ⟨"f", ()⟩ none) (.fvar Core.coreLoc xId none))
        }

/-- info: ACCEPTED -/
#guard_msgs in
#eval programVerdict (blockProgram [selfRecursiveMember])

/-! ## Inline members are rejected -/

-- An inline member without the recursion flag is rejected for being inline.
private def inlineUnflaggedMember : Function :=
  { plainMember with attr := #[.inline] }

/--
info: REJECTED: recursive function 'f' cannot be marked inline
-/
#guard_msgs (whitespace := lax) in
#eval programVerdict (blockProgram [inlineUnflaggedMember])

/-! ## Invalid member signatures are rejected -/

/-- The first member calls `g`; the second member's duplicate formals make its signature invalid. -/
private def invalidLaterSignature : Core.Program :=
  blockProgram
    [{ name := ⟨"f", ()⟩, typeArgs := [], isRecursive := true,
       inputs := [(xId, LMonoTy.int)], output := LMonoTy.int,
       body := some (.app Core.coreLoc (.op Core.coreLoc ⟨"g", ()⟩ none)
                     (.fvar Core.coreLoc xId none)) },
     { name := ⟨"g", ()⟩, typeArgs := [], isRecursive := true,
       inputs := [(xId, LMonoTy.int), (xId, LMonoTy.int)], output := LMonoTy.int,
       body := some (.fvar Core.coreLoc xId none) }]

/--
info: REJECTED: Function 'g': duplicate parameter names [x, x]
-/
#guard_msgs (whitespace := lax) in
#eval programVerdict invalidLaterSignature

/-! Type aliases are accepted in mutually recursive signatures and calls. -/

/-- `AliasInt` names `int`; both members use it in their signatures and call each other. -/
private def aliasMutualProgram : Core.Program :=
  let aliasTy := LMonoTy.tcons "AliasInt" []
  { decls :=
      [.type (.syn { name := "AliasInt", typeArgs := [], type := LMonoTy.int }) .empty,
       .recFuncBlock
        [{ name := ⟨"f", ()⟩, typeArgs := [], isRecursive := true,
           inputs := [(xId, aliasTy)], output := aliasTy,
           body := some (.app Core.coreLoc (.op Core.coreLoc ⟨"g", ()⟩ none)
                         (.fvar Core.coreLoc xId none)) },
         { name := ⟨"g", ()⟩, typeArgs := [], isRecursive := true,
           inputs := [(xId, aliasTy)], output := aliasTy,
           body := some (.app Core.coreLoc (.op Core.coreLoc ⟨"f", ()⟩ none)
                         (.fvar Core.coreLoc xId none)) }] .empty] }

/-- info: ACCEPTED -/
#guard_msgs in
#eval programVerdict aliasMutualProgram

/-- Does `es` carry at least one type annotation, with every annotation the type `int`? -/
private def clausesAtInt (es : List Core.Expression.Expr) : Bool :=
  Lambda.allExprsTys (fun mty => mty == LMonoTy.int) es &&
    !Lambda.allExprsTys (fun mty => mty != LMonoTy.int) es

/-! ## Recursive function clauses use the formal's type -/

/-- A recursive function with formal `y : int` whose precondition and measure compare `y`,
    annotated `ann`, with itself. -/
private def clauseRecPgmWith (ann : Option LMonoTy) : Core.Program :=
  let yOcc : Core.Expression.Expr := LExpr.fvar Core.coreLoc "y" ann
  { decls := [
    .recFuncBlock
      [{ name := "f", typeArgs := [], isRecursive := true,
         inputs := [("y", LMonoTy.int)], output := LMonoTy.int,
         body := some (LExpr.fvar Core.coreLoc "y" none),
         preconditions := [{ expr := LExpr.eq Core.coreLoc yOcc yOcc, md := Core.coreLoc }],
         measure := some (LExpr.ite Core.coreLoc (LExpr.eq Core.coreLoc yOcc yOcc)
           (LExpr.intConst Core.coreLoc 0) (LExpr.intConst Core.coreLoc 1)) }] .empty ]}

/-- Whether every recursive member's precondition and measure are annotated at `int`. -/
private def clauseRecVerdict (pgm : Core.Program) : Format :=
  match Core.Program.typeCheck initTyContext Lambda.TEnv.default pgm with
  | .error e => Std.format e
  | .ok (p', _) =>
    let funcs := p'.decls.flatMap fun
      | .recFuncBlock fs _ => fs
      | _ => []
    f!"precondition at int: {funcs.all (fun d => clausesAtInt (d.preconditions.map (·.expr)))}\n\
       measure at int: {funcs.all (fun d => clausesAtInt d.measure.toList)}"

/--
info: precondition at int: true
measure at int: true
-/
#guard_msgs (whitespace := lax) in
#eval clauseRecVerdict (clauseRecPgmWith none)

-- An annotation at a type variable the member does not declare is not in scope.
/--
info: Function 'f': type variable `a` is not in scope
-/
#guard_msgs (whitespace := lax) in
#eval clauseRecVerdict (clauseRecPgmWith (some (.ftvar "a")))

/-! ## A renamed type parameter avoids the type variables of the member's body

A member's type parameter with a reserved prefix is renamed for its signature stub as for the
full member, so the new name avoids a type variable written only in the body. -/

/-- A declared function with type parameter `a`. -/
private def polyIdDecl : Core.Decl :=
  .func { name := ⟨"polyId", ()⟩, typeArgs := ["a"], inputs := [(xId, .ftvar "a")],
          output := .ftvar "a" } .empty

/-- A recursive member with type parameter `$__ty0` that calls itself on `polyId x`, where the
    call of `polyId` is annotated `a → a`. -/
private def reservedParamMember : Function :=
  { name := ⟨"f", ()⟩, typeArgs := ["$__ty0"], isRecursive := true,
    inputs := [(xId, .ftvar "$__ty0")], output := .ftvar "$__ty0",
    body := some (.app Core.coreLoc (.op Core.coreLoc ⟨"f", ()⟩ none)
      (.app Core.coreLoc (.op Core.coreLoc ⟨"polyId", ()⟩ (some (.arrow (.ftvar "a") (.ftvar "a"))))
        (.fvar Core.coreLoc xId none))) }

/-- The type parameters and signature of each checked recursive member, or the error. -/
private def recMemberSignatures (pgm : Core.Program) : Format :=
  match Core.Program.typeCheck initTyContext Lambda.TEnv.default pgm with
  | .error e => Std.format e
  | .ok (p', _) =>
    Std.Format.joinSep (p'.decls.flatMap fun
      | .recFuncBlock fs _ =>
        fs.map fun f => f!"{f.name}<{f.typeArgs}> : {f.inputs.values} → {f.output}"
      | _ => []) Std.Format.line

/-- info: f<[a_1]> : [a_1] → a_1 -/
#guard_msgs (whitespace := lax) in
#eval recMemberSignatures { decls := [polyIdDecl, .recFuncBlock [reservedParamMember] .empty] }

-- The signature stub of the member has the same type parameter.
/-- info: f<[a_1]> : [a_1] → a_1 -/
#guard_msgs (whitespace := lax) in
#eval match RecFuncBlock.checkSignature initTyContext TEnv.default [reservedParamMember]
    reservedParamMember with
  | .error e => IO.println e
  | .ok sig =>
    let stub := sig.stub
    IO.println f!"{stub.name}<{stub.typeArgs}> : {stub.inputs.values} → {stub.output}"

end RecFuncBlock
end Core

end
