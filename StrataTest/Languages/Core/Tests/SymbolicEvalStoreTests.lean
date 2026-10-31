/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Transform.NondetElim
meta import Strata.Languages.Core.DDMTransform.Translate
meta import StrataDDM.Elab
meta import StrataDDM.BuiltinDialects.Init
import StrataDDM.Integration.Lean.HashCommands

meta section

/-! # Symbolic evaluation keeps old and new values apart

Symbolic evaluation stores each variable's current value in terms of unknowns: the
initial values of parameters and locals, and the values `havoc` and nondeterministic
declarations produce. An unknown has a name no program name has, so a stored value never
mentions a variable the store binds. Each test below has a false assertion that must not
be reported as proved, or a true one that must be.
-/

namespace Strata.SymbolicEvalStoreTests

private def quiet : Core.VerifyOptions := { Core.VerifyOptions.default with verbose := .quiet }

/-- `hd(l)` is the value `y` had when `l` was declared, not the assigned one: the assertion
fails. -/
private def destructorOfStored :=
#strata
program Core;
datatype IntList { Nil(), Cons(hd: int, tl: IntList) };
procedure P()
{
  var y : int;
  var l : IntList := Cons(y, Nil());
  y := 5;
  assert [a]: IntList..hd(l) == 5;
};
#end

/--
info:
Obligation: assert_a_calls_IntList..hd_0
Property: assert
Result: ✅ pass

Obligation: a
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify destructorOfStored (options := quiet)

/-- The `z` declared after the `if` is a new unknown, not the else branch's `z`: the assertion
fails. -/
private def mergeThenDeclare :=
#strata
program Core;
procedure P(b : bool)
{
  var x : int := 0;
  if (b) {
    x := 1;
  } else {
    var z : int;
    x := z;
  }
  var z : int;
  assume [h]: z == 5;
  assert [a]: !b ==> x == 5;
};
#end

/--
info:
Obligation: a
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify mergeThenDeclare (options := quiet)

/-- The same through a merge the path cap makes: the assertion fails. -/
private def pathCapMerge :=
#strata
program Core;
procedure P(b : bool)
{
  var x : int := 0;
  l: {
    if (b) { x := 1; } else { var z : int; x := z; exit l; }
  }
  var z : int;
  assume [h]: z == 5;
  assert [a]: !b ==> x == 5;
};
#end

/--
info:
Obligation: a
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify pathCapMerge (options := { quiet with pathCap := some 1 })

/-- A local named `y@1` is not the parameter's initial value: the assertion fails. -/
private def localNamedLikeUnknown :=
#strata
program Core;
datatype IntList { Nil(), Cons(hd: int, tl: IntList) };
procedure P(inout y : int)
{
  var l : IntList := Cons(y, Nil());
  y := 7;
  var y@1 : int;
  assume [h]: y@1 == 5;
  assert [a]: IntList..hd(l) == 5;
};
#end

/--
info:
Obligation: assert_a_calls_IntList..hd_0
Property: assert
Result: ✅ pass

Obligation: a
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify localNamedLikeUnknown (options := quiet)

/-- `old(y)` is not the local `y@1`: the postcondition fails. -/
private def oldNamedLikeUnknown :=
#strata
program Core;
procedure P(inout y : int)
spec {
  ensures [e]: old(y) == 5;
}
{
  var y@1 : int;
  assume [h]: y@1 == 5;
  y := y@1;
};
#end

/--
info:
Obligation: e
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify oldNamedLikeUnknown (options := quiet)

/-- The parameter `c` is not the function `c@1`: the assertion fails. -/
private def functionNamedLikeUnknown :=
#strata
program Core;
function |c@1|() : int;
axiom [ax]: |c@1|() == 5;
procedure P(c : int)
{
  assert [a]: c == 5;
};
#end

/--
info:
Obligation: a
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify functionNamedLikeUnknown (options := quiet)

/-- The local `c` is not the function `c`: the assertion fails. -/
private def localNamedLikeFunction :=
#strata
program Core;
function c() : int;
axiom [ax]: c() == 5;
procedure P()
{
  var c : int;
  assert [a]: c == 5;
};
#end

/--
info:
Obligation: a
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify localNamedLikeFunction (options := quiet)

/-- Each branch declares its own `z`, of different types: the assertion holds. -/
private def branchLocalsOfTwoTypes :=
#strata
program Core;
procedure P(b : bool)
{
  var x : int := 0;
  if (b) {
    var z : int;
    assume [h1]: int.lt(3, z);
    x := z;
  } else {
    var z : bool;
    assume [h2]: z;
    x := 1;
  }
  assert [a]: int.lt(0, x);
};
#end

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify branchLocalsOfTwoTypes (options := quiet)

/-- A value that doubles 40 times stays cheap to evaluate: the assertion holds. -/
private def doubling :=
#strata
program Core;
procedure P(x0 : int)
{
  var x : int := x0;
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  x := int.add(x, x);
  assert [a]: x0 == x0;
};
#end

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify doubling (options := quiet)

/-- `old(x)` is the parameter's initial value, which the precondition constrains: the
assertion holds. -/
private def initFromOld :=
#strata
program Core;
procedure P(inout x : int)
spec {
  requires [r]: int.gt(x, 0);
}
{
  var y : int := old(x);
  assert [a]: int.gt(y, 0);
};
#end

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify initFromOld (options := quiet)

/-- An `if` guard reads `old(x)` as the parameter's initial value: the assertion holds. -/
private def guardReadsOld :=
#strata
program Core;
procedure P(inout x : int)
spec {
  requires [r]: int.gt(x, 0);
}
{
  if (int.gt(old(x), 0)) { x := 1; } else { x := 2; }
  assert [a]: x == 1;
};
#end

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify guardReadsOld (options := quiet)

/-- An in-out parameter assigned in both branches holds the branch's value: the
assertion holds. -/
private def inoutBothBranches :=
#strata
program Core;
procedure P(inout x : int, b : bool)
{
  if (b) { x := 1; } else { x := 2; }
  assert [a]: b ==> x == 1;
};
#end

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify inoutBothBranches (options := quiet)

/-- After paths split by `exit` are merged, `old(x)` is the initial value, which the
precondition constrains: the assertion holds, with and without the path cap. -/
private def oldAfterExitMerge :=
#strata
program Core;
procedure P(inout x : int, b : bool)
spec {
  requires [r]: int.gt(x, 0);
}
{
  l: {
    if (b) { x := 1; exit l; } else { x := 2; }
  }
  assert [a]: int.gt(old(x), 0);
};
#end

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify oldAfterExitMerge (options := quiet)

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify oldAfterExitMerge (options := { quiet with pathCap := some 1 })

/-- A local named `|old x@0|` gets an unknown of its own, not the name `old x` that the
procedure scope binds: the obligation for `a` is about that unknown, so it does not hold. -/
private def localNamedLikeOld :=
#strata
program Core;
datatype IntList { Nil(), Cons(hd: int, tl: IntList) };
procedure P(inout x : int)
spec {
  requires [r]: x == 1;
}
{
  var |old x@0| : int;
  var l : IntList := Cons(|old x@0|, Nil());
  assert [a]: IntList..hd(l) == 1;
};
#end

/--
info:
Obligation: assert_a_calls_IntList..hd_0
Property: assert
Result: ✅ pass

Obligation: a
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify localNamedLikeOld (options := quiet)

/-- For an in-out parameter `x`, `old x` names x's initial value, so a local named `|old x|`
is rejected. -/
private def localNamedOld :=
#strata
program Core;
procedure P(inout x : int)
{
  var |old x| : int := 10;
  assert [c]: old x == 11;
};
#end

/--
error: ❌ Type checking error.
Variable old x of type int already in context.
-/
#guard_msgs in
#eval Core.verify localNamedOld (options := quiet)

/-- A name `old x` denotes the initial value of an in-out parameter `x`, so an input parameter
named `|old x|` is rejected. -/
private def inputNamedOld :=
#strata
program Core;
procedure P(inout x : int, |old x| : int)
{ };
#end

/--
error: ❌ Type checking error.
[P] Parameter old x: a name starting with "old " denotes the initial value of an in-out parameter!
-/
#guard_msgs in
#eval Core.verify inputNamedOld (options := quiet)

/-- An output parameter named `|old x|` is rejected. -/
private def outputNamedOld :=
#strata
program Core;
procedure P(inout x : int, out |old x| : int)
{ };
#end

/--
error: ❌ Type checking error.
[P] Parameter old x: a name starting with "old " denotes the initial value of an in-out parameter!
-/
#guard_msgs in
#eval Core.verify outputNamedOld (options := quiet)

/-! ## No obligation mentions a program variable

Every free variable of symbolic evaluation's output is an unknown, so none is a name the
program uses for a function, a parameter, a local or an `old` value. -/

private def translateCore (p : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

private def elimNondet (p : Core.Program) : Core.Program :=
  let (res, _) := StateT.run (ExceptT.run (Core.NondetElim.nondetElim p))
    Core.Transform.CoreTransformState.emp
  match res with | .ok (_, p') => p' | .error _ => p

/-- The program's functions, and every procedure's parameters, locals and `old` names. -/
private def programVarNames (p : Core.Program) : List String :=
  p.funcNames ++ p.decls.flatMap fun d =>
    match d with
    | .proc q _ =>
      (q.header.inputs.keys ++ q.header.outputs.keys).flatMap
        (fun x => [x.name, (Core.CoreIdent.mkOld x.name).name]) ++
      (Imperative.Block.definedVars (P := Core.Expression) (C := Core.Command)
        d.statements false).map (·.name)
    | _ => []

/-- The program names that symbolic evaluation's output mentions as free variables. -/
private def leakedNames (p : StrataDDM.Program) : List String :=
  match Core.typeCheck .quiet (translateCore p) with
  | .error _ => ["<type checking failed>"]
  | .ok tp =>
    match Core.toCoreProofObligationProgram .quiet (elimNondet tp) with
    | .error _ => ["<symbolic evaluation failed>"]
    | .ok (out, _) =>
      let names := programVarNames tp
      ((out.decls.flatMap fun d => Core.Statements.allExprs d.statements ++ d.ownExprs).flatMap
        fun e => e.freeVars.map (·.1.name)).filter names.contains |>.eraseDups

#guard [destructorOfStored, mergeThenDeclare, pathCapMerge, localNamedLikeUnknown,
        oldNamedLikeUnknown, functionNamedLikeUnknown, localNamedLikeFunction,
        branchLocalsOfTwoTypes, doubling, initFromOld,
        guardReadsOld, inoutBothBranches, oldAfterExitMerge,
        localNamedLikeOld].all (leakedNames · == [])

/-- The obligations symbolic evaluation produces for `p`. -/
private def obligations (p : StrataDDM.Program) : Std.Format :=
  match Core.typeCheck .quiet (translateCore p) with
  | .error _ => "<type checking failed>"
  | .ok tp =>
    match Core.toCoreProofObligationProgram .quiet (elimNondet tp) with
    | .error _ => "<symbolic evaluation failed>"
    | .ok (out, _) => Std.format out

/--
info: program Core;

datatype IntList {
  Nil(),
  Cons(hd : int, tl : IntList)
};
procedure P ()
{
  assume [r]: x@1 == 1;
  assert [a]: |old x@1| == 1;
};
-/
#guard_msgs in
#eval obligations localNamedLikeOld

/-! ## Deeply nested occurrences

The programs are built as text, without the `program Core;` header, and parsed when the
test runs: Lean does not compile a `#strata` term nested this deep. Symbolic evaluation's
fuel is 200 nesting levels. Each failing program assumes a fact about the initial `x`, assigns
`x`, and asserts the same expression, which then reads the assigned `x` and is false. -/

open Strata.CoreDDM StrataDDM in
private def parseCore (text : String) : IO StrataDDM.Program := do
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[initDialect, Core]
  let inputCtx := StrataDDM.Parser.stringInputContext ⟨"symbolic-eval-store-test"⟩ text
  StrataDDM.Elab.parseStrataProgramFromDialect dialects "Core" inputCtx

private def verifyText (text : String) : IO Unit := do
  IO.println (← Core.verify (← parseCore text) (options := quiet))

/-- `x + n`, written as `n` nested additions of 1. -/
private def addChain (x : String) (n : Nat) : String :=
  n.fold (fun _ _ t => s!"int.add({t}, 1)") x

/-- A list of `n` elements whose last one is `x`. -/
private def consSpine (x : String) (n : Nat) : String :=
  (n - 1).fold (fun _ _ t => s!"Cons(0, {t})") s!"Cons({x}, Nil())"

/-- `x == 0` under `n - 1` conjunctions with `b`. -/
private def andChain (n : Nat) : String :=
  (n - 1).fold (fun _ _ t => s!"b && ({t})") "x == 0"

/-- `x + n == n` with `x` nested `n` deep: the assumption makes the initial `x` 0, and after
`x := 1` the assertion is false, so it fails. -/
private def addChainProgram (n : Nat) : String :=
  s!"procedure P(inout x : int)
\{
  assume [h]: {addChain "x" n} == {n};
  x := 1;
  assert [a]: {addChain "x" n} == {n};
};"

/-- `l` equals a list of length `n` ending in `x`: after `x := x + 1` the same list ends in a
different value, so the assertion fails. -/
private def consSpineProgram (n : Nat) : String :=
  s!"datatype IntList \{ Nil(), Cons(hd: int, tl: IntList) };
procedure P(inout x : int, l : IntList)
\{
  assume [h]: l == {consSpine "x" n};
  x := int.add(x, 1);
  assert [a]: l == {consSpine "x" n};
};"

/-- `x == 0` nested `n` deep in a conjunction: the assumption makes the initial `x` 0, and
after `x := 1` the assertion is false, so it fails. -/
private def andChainProgram (n : Nat) : String :=
  s!"procedure P(inout x : int, b : bool)
\{
  assume [h]: {andChain n};
  x := 1;
  assert [a]: {andChain n};
};"

/-- `y` is declared as `x + n` with `x` nested `n` deep, and nothing is assigned after:
the assertion `y == x + n` holds. -/
private def deepCopyProgram (n : Nat) : String :=
  s!"procedure P(x : int)
\{
  var y : int := {addChain "x" n};
  assert [a]: y == {addChain "x" n};
};"

/--
info:
Obligation: a
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verifyText (addChainProgram 150)

/--
info:
Obligation: a
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verifyText (addChainProgram 199)

/--
info:
Obligation: a
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verifyText (addChainProgram 200)

/--
info:
Obligation: a
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verifyText (addChainProgram 250)

/--
info:
Obligation: a
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verifyText (consSpineProgram 199)

/--
info:
Obligation: a
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verifyText (andChainProgram 199)

/--
info:
Obligation: a
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verifyText (consSpineProgram 250)

/--
info:
Obligation: a
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verifyText (andChainProgram 250)

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verifyText (deepCopyProgram 250)

/-- info: [] -/
#guard_msgs in
#eval do
  let mut leaked := []
  for text in [addChainProgram 250, consSpineProgram 250, andChainProgram 250,
               deepCopyProgram 250] do
    leaked := leaked ++ leakedNames (← parseCore text)
  IO.println leaked

end Strata.SymbolicEvalStoreTests

end
