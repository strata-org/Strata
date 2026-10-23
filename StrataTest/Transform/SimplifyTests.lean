/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Transform.Simplify
meta import Strata.Transform.PrecondElim
import StrataDDM.Integration.Lean.HashCommands

meta section

/-! ## Simplification tests

Each test prints the simplified program. See `Strata.Transform.Simplify` for which
rewrites it performs and why each is admitted.
-/

namespace Core.Simplify.Tests

open Strata

private def translateCore (p : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

/-- Translate and simplify, returning the transformed program. -/
private def simplifyProgram (p : StrataDDM.Program) : Core.Program :=
  match Core.Transform.run (translateCore p) Core.Simplify.runSimplify
      { Core.Transform.CoreTransformState.emp with factory := Core.Factory } with
  | .error e => panic! s!"Simplify failed: {e}"
  | .ok (_changed, program) => program

private def simplifyAndPrint (p : StrataDDM.Program) : IO Unit :=
  let s := (Core.formatProgram (simplifyProgram p)).pretty
  IO.print (s.toList.reverse.dropWhile (· == '\n') |>.reverse |> String.ofList)

/-- Size of the simplified program, for the growth checks. -/
private def simplifiedSize (p : StrataDDM.Program) : Nat :=
  (Core.formatProgram (simplifyProgram p)).pretty.length

/-! ### An `inline` function is expanded only where expanding it simplifies

`dup` mentions its parameter twice, so expanding a call copies the argument twice.
That pays for itself when the copies fold into a constant and costs when they do
not, which is the whole of the admission rule. -/

private def dupSelective :=
#strata
program Core;

inline function dup (v : int) : int { int.add(v, v) }

procedure p (x : int)
{
  var concrete : int := dup(3);
  var symbolic : int := dup(x);
  var nested : int := dup(dup(dup(x)));
  assert [both]: int.ge(int.add(concrete, int.add(symbolic, nested)), 0);
};
#end

/-- info: program Core;

inline function dup (v : int) : int {
  int.add(v, v)
}
procedure p (x : int)
{
  var symbolic : int := int.add(x, x);
  var nested : int := dup(dup(int.add(x, x)));
  assert [both]: int.ge(int.add(6, int.add(symbolic, nested)), 0);
}; -/
#guard_msgs in
#eval simplifyAndPrint dupSelective

/-! ### Expanding is admitted when the body is smaller than the call

The rule is not "never expand". `unwrap` mentions its parameter once, so expanding
it always shrinks the term, symbolic argument or not. -/

private def expandWhenSmaller :=
#strata
program Core;

inline function unwrap (v : int) : int { v }

procedure p (x : int)
{
  assert [ok]: int.ge(unwrap(unwrap(x)), 0);
};
#end

/-- info: program Core;

inline function unwrap (v : int) : int {
  v
}
procedure p (x : int)
{
  assert [ok]: int.ge(x, 0);
}; -/
#guard_msgs in
#eval simplifyAndPrint expandWhenSmaller

/-! ### Growth of the nested case

Keeping a call that does not simplify is what bounds the output: the simplified
program grows by a constant per nesting level, where expanding every call would
double. The guard states that; the sizes below it record what the growth actually is,
so a change in either the property or the constant is visible. -/

private def nested4 :=
#strata
program Core;
inline function dup (v : int) : int { int.add(v, v) }
procedure p (x : int)
{
  assert [ok]: int.ge(dup(dup(dup(dup(x)))), 0);
};
#end

private def nested8 :=
#strata
program Core;
inline function dup (v : int) : int { int.add(v, v) }
procedure p (x : int)
{
  assert [ok]: int.ge(dup(dup(dup(dup(dup(dup(dup(dup(x)))))))), 0);
};
#end

#guard simplifiedSize nested8 < 2 * simplifiedSize nested4

/-- info: 154 174 -/
#guard_msgs in
#eval IO.println s!"{simplifiedSize nested4} {simplifiedSize nested8}"

/-! ### A variable's value is substituted only where that does not grow the term

A value of a single node can always replace the name, since a name for a name cannot
grow the term. Beyond one node the substitution has to pay for itself where the value
is used: it is admitted when the result folds smaller and declined otherwise, which is
what stops a value being copied to every one of its uses. -/

private def substSelective :=
#strata
program Core;

datatype List () { Nil(), Cons(head: int, tail: List) };

procedure p (x : int)
{
  var alias : int := x;
  var wide : int := int.add(x, 1);
  var built : List := Cons(7, Nil());
  assert [aliasSubstituted]: int.ge(alias, 0);
  assert [wideKept]: int.ge(wide, 0);
  assert [builtFoldsAtUse]: int.ge(List..head(built), 0);
};
#end

/-- info: program Core;

datatype List {
  Nil(),
  Cons(head : int, tail : List)
};
procedure p (x : int)
{
  var wide : int := int.add(x, 1);
  assert [aliasSubstituted]: int.ge(x, 0);
  assert [wideKept]: int.ge(wide, 0);
  assert [builtFoldsAtUse]: true;
}; -/
#guard_msgs in
#eval simplifyAndPrint substSelective

/-! ### Constant folding, and a decided equality -/

private def folding :=
#strata
program Core;
procedure p (x : int)
{
  var a : int := int.add(2, 3);
  var b : bool := int.lt(1, 2);
  assert [ok]: b && int.ge(a, 5);
};
#end

/-- info: program Core;

procedure p (x : int)
{
  assert [ok]: true;
}; -/
#guard_msgs in
#eval simplifyAndPrint folding

/-! ### A decided `if` is kept, with its guard and branch conditions folded

This phase does not eliminate a decided `if`. Symbolic evaluation, which still runs
after it, is what turns a decided `if` into obligations and gives a dead branch's
assertions and covers their unreachable semantics. So the `if` is left standing with
its guard folded to a constant and each branch simplified; here `var a := 1` folds
every use away and is then dropped as dead. -/

private def decidedIf :=
#strata
program Core;
procedure p (x : int)
{
  var a : int := 1;
  if (int.gt(a, 0)) {
    assert [live]: int.ge(a, 1);
  } else {
    assert [dead]: int.le(a, 0);
    cover [unreachable]: int.ge(x, 0);
  }
};
#end

/-- info: program Core;

procedure p (x : int)
{
  if (true) {
    assert [live]: true;
  } else {
    assert [dead]: false;
    cover [unreachable]: int.ge(x, 0);
  }
}; -/
#guard_msgs in
#eval simplifyAndPrint decidedIf

/-! ### A decided `if` carries the live arm's values past it

Only the arm the guard selects can run, so what it leaves a variable holding is what
the variable holds after the branch, whatever the dead arm assigns. The branch itself
stays, as in `decidedIf`. Here `a` is `5` after the first branch, so the second guard
folds too and its live arm makes `a` `6`, which is what the assertion then reads. -/

private def decidedIfCarries :=
#strata
program Core;
procedure p (x : int)
{
  var a : int := 3;
  if (int.gt(a, 0)) {
    a := 5;
  } else {
    a := x;
  }
  if (int.gt(a, 4)) {
    a := int.add(a, 1);
  }
  assert [ok]: (a == 6);
};
#end

/-- info: program Core;

procedure p (x : int)
{
  var a : int := 3;
  if (true) {
    a := 5;
  } else {
    a := x;
  }
  if (true) {
    a := 6;
  }
  assert [ok]: true;
}; -/
#guard_msgs in
#eval simplifyAndPrint decidedIfCarries

/-! ### A closed value is copied freely

A canonical value mentions no variable, so copying it cannot expose another variable to
copy in turn. It is therefore substituted at every use, and a call whose arguments are
all canonical is expanded even when its body mentions a parameter twice, because the
expansion folds against closed values. Together with `decidedIfCarries` this is what
keeps a concrete list concrete through a decided branch: `headOr` reads `3`, the guard
folds, the live arm's list is carried past the branch, and the final read folds too. -/

private def closedValuesCopy :=
#strata
program Core;

datatype List () { Nil(), Cons(head: int, tail: List) };

inline function headOr (xs : List, d : int) : int {
  if List..isCons(xs) then List..head(xs) else d
}

procedure p ()
{
  var xs : List := Cons(3, Cons(1, Nil()));
  var h : int := headOr(xs, 0);
  if (int.gt(h, 2)) {
    xs := Cons(1, Cons(3, Nil()));
  }
  assert [sorted]: (headOr(xs, 0) == 1);
};
#end

/-- info: program Core;

datatype List {
  Nil(),
  Cons(head : int, tail : List)
};
inline function headOr (xs : List, d : int) : int {
  if List..isCons(xs) then List..head(xs) else d
}
procedure p ()
{
  var xs : List := Cons(3, Cons(1, Nil));
  if (true) {
    xs := Cons(1, Cons(3, Nil));
  }
  assert [sorted]: true;
}; -/
#guard_msgs in
#eval simplifyAndPrint closedValuesCopy

/-! ### A substitution that exposes a variable is followed through

Substituting `z` into the guard leaves `List..isCons(x)`, which mentions `x` although the
guard did not. `x` is tried in turn, the guard folds to `true`, and the live arm's
value of `r` reaches the assertion. Without the second step the guard would stay
open here while symbolic evaluation, which substitutes every value, decides it. -/

private def exposedChain :=
#strata
program Core;

datatype List () { Nil(), Cons(head: int, tail: List) };

procedure p (y : int, out r : int)
{
  var x : List := Cons(y, Nil());
  var z : List := Cons(1, x);
  if (List..isCons(List..tail(z))) {
    r := 1;
  } else {
    r := 0;
  }
  assert [r1]: (r == 1);
};
#end

/-- info: program Core;

datatype List {
  Nil(),
  Cons(head : int, tail : List)
};
procedure p (y : int, out r : int)
{
  var x : List := Cons(y, Nil);
  var z : List := Cons(1, x);
  if (true) {
    r := 1;
  } else {
    r := 0;
  }
  assert [r1]: true;
}; -/
#guard_msgs in
#eval simplifyAndPrint exposedChain

/-! ### A constructor argument is expanded when the result folds smaller

`getOr` mentions its parameter twice and receives `Some(int.add(x, 1))`, which is neither
closed nor a single node, so the shape test alone declines it. But the body tests and
destructs that parameter, so with a constructor in its place both copies fold away. The
expansion is kept because its folded result is smaller than the call. -/

private def constrArgExpands :=
#strata
program Core;

datatype Opt () { None(), Some(v: int) };

inline function getOr (o : Opt, d : int) : int {
  if Opt..isSome(o) then Opt..v(o) else d
}

procedure p (x : int)
{
  assert [ok]: int.ge(getOr(Some(int.add(x, 1)), 0), 0);
};
#end

/-- info: program Core;

datatype Opt {
  None(),
  Some(v : int)
};
inline function getOr (o : Opt, d : int) : int {
  if Opt..isSome(o) then Opt..v(o) else d
}
procedure p (x : int)
{
  assert [ok]: int.ge(int.add(x, 1), 0);
}; -/
#guard_msgs in
#eval simplifyAndPrint constrArgExpands

/-! ### Assumptions and assertions that simplify to `true` both stay

`assume true` stays so that the program's events correspond one for one; the
evaluator adds no path condition for it. `assert true` stays: it is still an
obligation, and one that is answered without a solver. -/

private def assumeAssert :=
#strata
program Core;
procedure p (x : int)
{
  assume [triv]: int.ge(1, 0);
  assert [triv2]: int.ge(2, 0);
  assert [real]: int.ge(x, 0);
};
#end

/-- info: program Core;

procedure p (x : int)
{
  assume [triv]: true;
  assert [triv2]: true;
  assert [real]: int.ge(x, 0);
}; -/
#guard_msgs in
#eval simplifyAndPrint assumeAssert

/-! ### A havoc'd variable has no known value

Substituting the value a variable had before it was havoc'd would be unsound, so
the value is forgotten rather than kept. -/

private def havocForgets :=
#strata
program Core;
procedure p (x : int)
{
  var a : int := 3;
  havoc a;
  assert [ok]: int.ge(a, 0);
};
#end

/-- info: program Core;

procedure p (x : int)
{
  var a : int := 3;
  havoc a;
  assert [ok]: int.ge(a, 0);
}; -/
#guard_msgs in
#eval simplifyAndPrint havocForgets

/-! ### A variable written in an undecided branch is forgotten after it -/

private def branchForgets :=
#strata
program Core;
function g (x : int) : int;
procedure p (x : int)
{
  var a : int := 3;
  if (int.gt(g(x), 0)) {
    a := 4;
  }
  assert [ok]: int.ge(a, 0);
};
#end

/-- info: program Core;

function g (x : int) : int;
procedure p (x : int)
{
  var a : int := 3;
  if (int.gt(g(x), 0)) {
    a := 4;
  }
  assert [ok]: int.ge(a, 0);
}; -/
#guard_msgs in
#eval simplifyAndPrint branchForgets

/-! ### A branch write invalidates a value that merely mentions the variable

`b` records `int.add(x, 1)`, which mentions `x` but is not `x`. The branch writes `x`,
so `b`'s recording is stale afterwards even though nothing wrote `b`. This is the
`ite` path to the same invalidation `dependentForgets` reaches through `havoc`, so
`b` keeps being read rather than substituted.

`x` is declared without a value on purpose: given one, it would be substituted into
`b`'s definition and `b` would no longer mention `x`, leaving nothing for the branch
write to invalidate. -/

private def branchForgetsDependent :=
#strata
program Core;
function g (x : int) : int;
procedure p (n : int)
{
  var x : int;
  var b : int := int.add(x, 1);
  if (int.gt(g(n), 0)) {
    x := 7;
  }
  assert [dependentForgotten]: int.ge(b, 0);
};
#end

/-- info: program Core;

function g (x : int) : int;
procedure p (n : int)
{
  var x : int;
  var b : int := int.add(x, 1);
  if (int.gt(g(n), 0)) {
    x := 7;
  }
  assert [dependentForgotten]: int.ge(b, 0);
}; -/
#guard_msgs in
#eval simplifyAndPrint branchForgetsDependent

/-! ### A block scopes its declarations but not its writes

Three things have to hold at a block boundary: a value known before the block is
available inside it, it survives a block that does not write it, and it is forgotten
after a block that does — while a variable that same block did not write is still
known, so a block forgets its write set rather than everything in scope. -/

private def blockScoping :=
#strata
program Core;
function g (x : int) : int;
procedure p (x : int)
{
  var outer : int := 3;
  var w : int := 7;
  readOnly: {
    var inner : int := 4;
    assert [inside]: int.ge(int.add(outer, inner), 0);
  }
  assert [afterReadOnly]: int.ge(outer, 0);
  writes: {
    w := g(x);
  }
  assert [outerSurvivesWrite]: int.ge(outer, 0);
  assert [afterWrite]: int.ge(w, 0);
};
#end

/-- info: program Core;

function g (x : int) : int;
procedure p (x : int)
{
  var w : int := 7;
  readOnly: {
    assert [inside]: true;
  }
  assert [afterReadOnly]: true;
  writes: {
    w := g(x);
  }
  assert [outerSurvivesWrite]: true;
  assert [afterWrite]: int.ge(w, 0);
}; -/
#guard_msgs in
#eval simplifyAndPrint blockScoping

/-! ### A dead definition inside a loop body is dropped

The sweep reaches into a loop body as it does into a branch; `dropDeadDefs` documents
why that is sound for a body that repeats. `deadInsideNestedLoop` drives the recursive
descent through two layers, and `liveInsideLoop` is the counterpart showing a body-local
that IS read survives. -/

private def deadInsideLoop :=
#strata
program Core;
procedure p (n : int)
{
  var i : int := 0;
  while (int.lt(i, n))
  {
    var dead : int := 5;
    i := int.add(i, 1);
  }
};
#end

/-- info: program Core;

procedure p (n : int)
{
  var i : int := 0;
  while (int.lt(i, n))
  {
    i := int.add(i, 1);
  }
}; -/
#guard_msgs in
#eval simplifyAndPrint deadInsideLoop

private def deadInsideNestedLoop :=
#strata
program Core;
procedure p (n : int)
{
  var i : int := 0;
  while (int.lt(i, n))
  {
    var dead1 : int := 5;
    while (int.lt(i, n))
    {
      var dead2 : int := 7;
      i := int.add(i, 1);
    }
  }
};
#end

/-- info: program Core;

procedure p (n : int)
{
  var i : int := 0;
  while (int.lt(i, n))
  {
    while (int.lt(i, n))
    {
      i := int.add(i, 1);
    }
  }
}; -/
#guard_msgs in
#eval simplifyAndPrint deadInsideNestedLoop

private def liveInsideLoop :=
#strata
program Core;
procedure p (x : int, n : int)
{
  var i : int := 0;
  while (int.lt(i, n))
  {
    var step : int := int.add(x, 1);
    i := int.add(i, step);
  }
};
#end

/-- info: program Core;

procedure p (x : int, n : int)
{
  var i : int := 0;
  while (int.lt(i, n))
  {
    var step : int := int.add(x, 1);
    i := int.add(i, step);
  }
}; -/
#guard_msgs in
#eval simplifyAndPrint liveInsideLoop

/-! ### A variable a loop body writes is forgotten

A loop body runs an unknown number of times, so a value known before the loop is not
known inside it or after it. Loops reach this through their own invalidation, applied
before the guard and body are simplified, rather than through the `ite` path that
`branchForgets` covers. -/

private def loopForgets :=
#strata
program Core;
procedure p (x : int)
{
  var a : int := 3;
  while (int.lt(a, 10))
  {
    a := int.add(a, 1);
  }
  assert [ok]: int.ge(a, 0);
};
#end

/-- info: program Core;

procedure p (x : int)
{
  var a : int := 3;
  while (int.lt(a, 10))
  {
    a := int.add(a, 1);
  }
  assert [ok]: int.ge(a, 0);
}; -/
#guard_msgs in
#eval simplifyAndPrint loopForgets

/-! ### A variable the loop body does not write stays known

Invalidation is confined to what the body writes. `k` survives the loop, so the
assertion after it folds and `k`'s definition is dropped, while `i` -- which the body
does write -- is forgotten and keeps being read. -/

private def loopKeepsUnwritten :=
#strata
program Core;
procedure p ()
{
  var k : int := 5;
  var i : int := 0;
  while (int.lt(i, 10))
  {
    i := int.add(i, 1);
  }
  assert [ok]: int.ge(k, 0);
};
#end

/-- info: program Core;

procedure p ()
{
  var i : int := 0;
  while (int.lt(i, 10))
  {
    i := int.add(i, 1);
  }
  assert [ok]: true;
}; -/
#guard_msgs in
#eval simplifyAndPrint loopKeepsUnwritten

/-! ### A definition the specification mentions survives the sweep

`r` is read by the `ensures` clause, so its assignment stays. `unused` is read by
nothing, but its right-hand side is not a value that surely evaluates, so the sweep
keeps it as well. -/

private def liveOutput :=
#strata
program Core;
procedure p (x : int, out r : int)
spec {
  ensures [post]: int.ge(r, 0);
}
{
  var unused : int := int.add(x, 1);
  r := 7;
};
#end

/-- info: program Core;

procedure p (x : int, out r : int)
spec {
  ensures [post]: int.ge(r, 0);
  } {
  var unused : int := int.add(x, 1);
  r := 7;
}; -/
#guard_msgs in
#eval simplifyAndPrint liveOutput

/-! ### A specification is simplified, not only a body

`requires` and `ensures` expressions go through the same rewrites as statements, with
an empty environment: folding applies, and nothing is substituted, because a parameter
has no value to substitute. So the closed `ensures` clause folds away entirely, while
the `requires` clause keeps its reference to `x` and is left as it stands. -/

private def specSimplified :=
#strata
program Core;
procedure p (x : int, out r : int)
spec {
  requires [pre]: int.ge(int.add(x, 3), 0);
  ensures [post]: int.ge(int.add(3, 4), 0);
}
{
  r := 7;
};
#end

/-- info: program Core;

procedure p (x : int, out r : int)
spec {
  requires [pre]: int.ge(int.add(x, 3), 0);
  ensures [post]: true;
  } {
  r := 7;
}; -/
#guard_msgs in
#eval simplifyAndPrint specSimplified

/-! ### A function declared in the body

Translation lowers a body-level function to a variable holding a lambda. The lambda
mentions no variable, so it is a closed value: it is substituted at the call, the
application reduces, and `twice(4)` folds to `8`. The assertion becomes `true` and both
definitions are then unread. -/

private def localFunc :=
#strata
program Core;
procedure p (x : int)
{
  inline function twice (v : int) : int { int.mul(2, v) }
  var a : int := twice(4);
  assert [ok]: int.ge(a, 0);
};
#end

/-- info: program Core;

procedure p (x : int)
{
  assert [ok]: true;
}; -/
#guard_msgs in
#eval simplifyAndPrint localFunc

/-! ### A definition read only by a body-level function survives

A body-level function becomes a lambda, and this one reads `captured` from the enclosing
scope. That lambda is not closed, so it is not substituted at its call, and its read of
`captured` keeps that definition alive. -/

private def localFuncKeepsAlive :=
#strata
program Core;
procedure p (n : int)
{
  var captured : int := int.add(n, 1);
  function usesCaptured (v : int) : int { int.add(v, captured) }
  var r : int := usesCaptured(2);
  assert [ok]: int.ge(r, 0);
};
#end

/-- info: program Core;

procedure p (n : int)
{
  var captured : int := int.add(n, 1);
  var usesCaptured : int -> int := fun v : int => int.add(v, captured);
  var r : int := usesCaptured(2);
  assert [ok]: int.ge(r, 0);
}; -/
#guard_msgs in
#eval simplifyAndPrint localFuncKeepsAlive

/-! ### Simplifying twice changes nothing

A second application leaves the result unchanged, on a program that exercises
expansion, folding and the sweep together. -/

private def idempotent (p : StrataDDM.Program) : Bool :=
  let once := (Core.formatProgram (simplifyProgram p)).pretty
  let twice := match Core.Transform.run (simplifyProgram p) Core.Simplify.runSimplify
      { Core.Transform.CoreTransformState.emp with factory := Core.Factory } with
    | .error _ => ""
    | .ok (_, prog) => (Core.formatProgram prog).pretty
  once == twice

/-- info: true true true true -/
#guard_msgs in
#eval IO.println s!"{idempotent dupSelective} {idempotent decidedIf} {idempotent folding} {idempotent liveOutput}"

/-! ### Datatype constructors, testers and destructors fold on a constructor

Constructor/tester/destructor functions carry `inlineIfConstr`/`evalIfConstr`, which
`fold` keeps (it strips only the unconditional `inline`). So a tester or destructor
applied to a constructor application folds, and a constructor with foldable arguments
is canonicalised. This is the simplification datatype-heavy code relies on. -/

private def datatypeFold :=
#strata
program Core;

datatype List () { Nil(), Cons(head: int, tail: List) };

procedure p ()
{
  var built : List := Cons(int.add(40, 2), Nil());
  var h : int := List..head(Cons(7, Nil()));
  var isc : bool := List..isCons(Cons(7, Nil()));
  var isn : bool := List..isNil(Cons(7, Nil()));
  assert [h7]: (h == 7);
  assert [c]: isc;
  assert [n]: !isn;
};
#end

/-- info: program Core;

datatype List {
  Nil(),
  Cons(head : int, tail : List)
};
procedure p ()
{
  assert [h7]: true;
  assert [c]: true;
  assert [n]: true;
}; -/
#guard_msgs in
#eval simplifyAndPrint datatypeFold

/-! ### A destructor on a symbolic list is kept

The selective rule applies to datatypes too: with the argument not a constructor,
`List..head(xs)` folds to nothing and is left as a call. -/

private def datatypeSymbolic :=
#strata
program Core;

datatype List () { Nil(), Cons(head: int, tail: List) };

procedure p (xs : List)
{
  var h : int := List..head(xs);
  assert [ok]: int.ge(h, 0);
};
#end

/-- info: program Core;

datatype List {
  Nil(),
  Cons(head : int, tail : List)
};
procedure p (xs : List)
{
  var h : int := List..head(xs);
  assert [ok]: int.ge(h, 0);
}; -/
#guard_msgs in
#eval simplifyAndPrint datatypeSymbolic

/-! ### A destructor on a symbolic value inside a known constructor still folds

`List..head(Cons(y, Nil()))` folds to `y` even when `y` is symbolic, because folding a
destructor needs only the outer constructor, not a ground argument. -/

private def datatypeSymbolicField :=
#strata
program Core;

datatype List () { Nil(), Cons(head: int, tail: List) };

procedure p (y : int)
{
  var h : int := List..head(Cons(y, Nil()));
  assert [ok]: int.ge(h, 0);
};
#end

/-- info: program Core;

datatype List {
  Nil(),
  Cons(head : int, tail : List)
};
procedure p (y : int)
{
  assert [ok]: int.ge(y, 0);
}; -/
#guard_msgs in
#eval simplifyAndPrint datatypeSymbolicField

/-! ### Unrecorded variables do not use up the substitution budget

The assertion mentions three parameters before `z`, and only `z` has a recorded value.
The parameters have nothing to substitute, so they must not spend the budget, which is
the number of recorded values: `z`'s value is still tried and `List..head(z)` folds. -/

private def substAfterUnrecorded :=
#strata
program Core;

datatype List () { Nil(), Cons(head: int, tail: List) };

procedure p (a : int, b : int, c : int, y : int)
{
  var z : List := Cons(y, Nil());
  assert [ok]: int.ge(int.add(int.add(a, b), List..head(z)), c);
};
#end

/-- info: program Core;

datatype List {
  Nil(),
  Cons(head : int, tail : List)
};
procedure p (a : int, b : int, c : int, y : int)
{
  var z : List := Cons(y, Nil);
  assert [ok]: int.ge(int.add(int.add(a, b), y), c);
}; -/
#guard_msgs in
#eval simplifyAndPrint substAfterUnrecorded

/-! ### A self-referential value is not recorded

`a := int.add(a, 1)` defines `a` in terms of itself. Recording that as `a`'s value
would let a later use substitute it, and the substituted term would mention `a`
again. The definition is kept and the assertion keeps reading the name. -/

private def selfReferential :=
#strata
program Core;
procedure p (x : int)
{
  var a : int;
  havoc a;
  a := int.add(a, 1);
  assert [ok]: int.ge(a, 0);
};
#end

/-- info: program Core;

procedure p (x : int)
{
  var a : int;
  havoc a;
  a := int.add(a, 1);
  assert [ok]: int.ge(a, 0);
}; -/
#guard_msgs in
#eval simplifyAndPrint selfReferential

/-! ### A value that mentions a mutated variable is forgotten too

`a`'s recorded value is `int.add(x, 1)`, which mentions `x`. Havoc'ing `x` makes
that recording stale even though `a` itself was not written, so it is dropped and
the assertion keeps reading `a`. -/

private def dependentForgets :=
#strata
program Core;
procedure p (x : int)
{
  var a : int := int.add(x, 1);
  havoc x;
  assert [ok]: int.ge(a, 0);
};
#end

/-- info: program Core;

procedure p (x : int)
{
  var a : int := int.add(x, 1);
  havoc x;
  assert [ok]: int.ge(a, 0);
}; -/
#guard_msgs in
#eval simplifyAndPrint dependentForgets

/-! ### A chain of expansions completes within the budget

Expanding a body can expose another call to expand, and that descent is bounded by
a budget rather than by the term measure. A chain well inside the budget must still
expand all the way: `ping` expands to a `pong` call, which expands to its argument,
so the assertion ends up reading `x` directly. -/

private def chainedExpansion :=
#strata
program Core;

inline function pong (n : int) : int { n }
inline function ping (n : int) : int { pong(n) }

procedure p (x : int)
{
  assert [ok]: int.ge(ping(ping(ping(x))), 0);
};
#end

/-- info: program Core;

inline function pong (n : int) : int {
  n
}
inline function ping (n : int) : int {
  pong(n)
}
procedure p (x : int)
{
  assert [ok]: int.ge(x, 0);
}; -/
#guard_msgs in
#eval simplifyAndPrint chainedExpansion

/-! ### A call invalidates the variables it writes

A call's `out` and `inout` arguments are written by the call, so a value recorded
for one of them before the call must not be substituted after it. `a` is `3` at the
call, and the assertion afterwards still reads `a`. -/

private def callWrites :=
#strata
program Core;

procedure q (inout n : int)
spec {
  ensures true;
}
{
  n := int.add(n, 1);
};

procedure p ()
{
  var a : int := 3;
  call q(inout a);
  assert [ok]: int.ge(a, 0);
};
#end

/-- info: program Core;

procedure q (inout n : int)
spec {
  ensures [q_ensures_0]: true;
  } {
  n := int.add(n, 1);
};
procedure p ()
{
  var a : int := 3;
  call q(inout a);
  assert [ok]: int.ge(a, 0);
}; -/
#guard_msgs in
#eval simplifyAndPrint callWrites

/-! ### A definition read only by a loop measure survives

The measure is a read like any other, so the definition it names is live and the
sweep must keep it. `measureKeepsAliveNondet` is the same check with a
nondeterministic guard, where the guard itself reads nothing and the measure is the
only reader left. -/

private def measureKeepsAlive :=
#strata
program Core;
procedure p (n : int)
{
  var bound : int := int.add(n, 1);
  var i : int := 0;
  while (int.lt(i, n))
    decreases int.sub(bound, i)
  {
    i := int.add(i, 1);
  }
};
#end

/-- info: program Core;

procedure p (n : int)
{
  var bound : int := int.add(n, 1);
  var i : int := 0;
  while (int.lt(i, n))
  decreases int.sub(bound, i)
  {
    i := int.add(i, 1);
  }
}; -/
#guard_msgs in
#eval simplifyAndPrint measureKeepsAlive

private def measureKeepsAliveNondet :=
#strata
program Core;
procedure p (n : int)
{
  var bound : int := int.add(n, 1);
  var i : int := 0;
  while *
    decreases int.sub(bound, i)
  {
    i := int.add(i, 1);
  }
};
#end

/-- info: program Core;

procedure p (n : int)
{
  var bound : int := int.add(n, 1);
  var i : int := 0;
  while *
  decreases int.sub(bound, i)
  {
    i := int.add(i, 1);
  }
}; -/
#guard_msgs in
#eval simplifyAndPrint measureKeepsAliveNondet

/-! ### A nondeterministically initialized variable has no value

There is nothing to substitute at a use, so the declaration stays. -/

private def nondetInit :=
#strata
program Core;
procedure p ()
{
  var a : int;
  assert [ok]: int.ge(a, 0);
};
#end

/-- info: program Core;

procedure p ()
{
  var a : int;
  assert [ok]: int.ge(a, 0);
}; -/
#guard_msgs in
#eval simplifyAndPrint nondetInit

/-! ### An assumption that does not fold is kept

The counterpart to `assumeAssert`: an `assume` whose condition does not fold to
`true` still carries information, so the statement survives. -/

private def assumeKept :=
#strata
program Core;
procedure p (x : int)
{
  assume [kept]: int.ge(int.add(x, 0), 0);
  assert [ok]: int.ge(x, 0);
};
#end

/-- info: program Core;

procedure p (x : int)
{
  assume [kept]: int.ge(int.add(x, 0), 0);
  assert [ok]: int.ge(x, 0);
}; -/
#guard_msgs in
#eval simplifyAndPrint assumeKept

/-! ### Expansion stops when the budget is exhausted

The budget bounds the depth of nested expansion. Setting it directly shows the bound
at each value; `inlineChain` shows the default bound on a parsed program.

The budget is spent on expansion *within* an expanded body, not on the number of
expansions performed. Hence one unit covers any depth of `unwrap` nesting, whose
body holds no further call, while `ping` — whose body calls `pong` — needs two. -/

private def unwrapTwice :=
#strata
program Core;

inline function unwrap (v : int) : int { v }

procedure p (x : int)
{
  assert [ok]: unwrap(unwrap(x));
};
#end

private def pingOnce :=
#strata
program Core;

inline function pong (n : int) : int { n }
inline function ping (n : int) : int { pong(n) }

procedure p (x : int)
{
  assert [ok]: ping(x);
};
#end

/-- The condition of the first `assert` in the first procedure of `p`. -/
private def firstAssertCond (prog : Core.Program) : Option Core.Expression.Expr :=
  prog.decls.findSome? fun d =>
    match d with
    | .proc pr _ =>
      match pr.body with
      | .structured ss =>
        ss.findSome? fun s =>
          match s with
          | .cmd (.cmd (.assert _ e _)) => some e
          | _ => none
      | .cfg _ => none
    | _ => none

/-- Simplify that condition with the expansion budget set to `fuel`. -/
private def simplifyWithFuel (p : StrataDDM.Program) (fuel : Nat) : String :=
  let prog := translateCore p
  match Core.Transform.run prog (fun q => do
      let F ← Core.Simplify.programFactory q
      pure (false, q, F))
      { Core.Transform.CoreTransformState.emp with factory := Core.Factory } with
  | .error _ => "factory build failed"
  | .ok (_, _, F) =>
    match firstAssertCond prog with
    | some e =>
      let ctx := { Core.Simplify.Ctx.ofFactory F with expandFuel := fuel }
      (Std.format (Core.Simplify.simplifyExpr ctx e)).pretty
    | none => "no assert found"

/-- info: unwrap, fuel 1: x
unwrap, fuel 0: unwrap(unwrap(x))
ping,   fuel 2: x
ping,   fuel 1: x -/
#guard_msgs in
#eval IO.println s!"unwrap, fuel 1: {simplifyWithFuel unwrapTwice 1}\nunwrap, fuel 0: {simplifyWithFuel unwrapTwice 0}\nping,   fuel 2: {simplifyWithFuel pingOnce 2}\nping,   fuel 1: {simplifyWithFuel pingOnce 1}"

/-! ### An expression under a binder is left alone

A binder's body is an open term: its bound variables refer to the binder, so folding
it in isolation would produce dangling indices. `int.add(2, 3)` therefore survives
inside the quantifier, where the same term folds to `5` outside one. -/

private def underBinder :=
#strata
program Core;
procedure p (x : int)
{
  var outside : int := int.add(2, 3);
  assert [ok]: (forall y : int :: int.ge(int.add(y, int.add(2, 3)), 0)) && int.ge(outside, 0);
};
#end

/-- info: program Core;

procedure p (x : int)
{
  assert [ok]: (forall y : int :: int.ge(int.add(y, int.add(2, 3)), 0)) && true;
}; -/
#guard_msgs in
#eval simplifyAndPrint underBinder

/-! ### An applied binder is reduced, an unapplied one is left alone

`have x : T = v in body` is sugar for an abstraction applied to `v`, so it is a redex.
The traversal does not descend through a binder, but it does not need to: the round's
fold reduces the application at the top level, and the body reaches the second
expansion pass as a closed term. The quantifier in `underBinder` is the contrasting
case — nothing applies it, so nothing inside it is touched. -/

private def appliedBinder :=
#strata
program Core;
procedure p (x : int)
{
  assert [reduced]: have y : int = 3 in int.add(y, y) == 6;
  assert [symbolicBinder]: have y : int = x in int.add(y, y) == int.mul(2, x);
};
#end

/-- info: program Core;

procedure p (x : int)
{
  assert [reduced]: true;
  assert [symbolicBinder]: int.add(x, x) == int.mul(2, x);
}; -/
#guard_msgs in
#eval simplifyAndPrint appliedBinder

/-! ### The factory reaching the phase is the pipeline's, not a fresh one

Earlier phases change the factory: monomorphization drops polymorphic entries and
adds specializations under mangled names, and a caller can supply extra functions.
A factory rebuilt from `Core.Factory` would resolve none of those, so a function
present only in the accumulated state must still reach the phase. -/

private def emptyProgram :=
#strata
program Core;
procedure p ()
{
  assert [ok]: true;
};
#end

/-- A function that exists only in the pipeline's factory, never in a program. -/
private def stateOnlyFunc : Lambda.LFunc Core.CoreLParams :=
  { name := "simplifyTestStateOnly", typeArgs := [], isConstr := false,
    inputs := [("n", .int)], output := .int, body := none, attr := #[], axioms := [] }

/-- What `programFactory` returns for a function the pipeline state carried in:
    its name, arity and output type, so a corrupted entry is caught rather than
    merely a missing one. -/
private def accumulatedFactoryReaches : String :=
  let seeded := Core.Factory.pushIfNew stateOnlyFunc
  match Core.Transform.run (translateCore emptyProgram)
      (fun q => do let F ← Core.Simplify.programFactory q; pure (false, q, F))
      { Core.Transform.CoreTransformState.emp with factory := seeded } with
  | .error _ => "factory build failed"
  | .ok (_, _, F) =>
    match F.get? "simplifyTestStateOnly" with
    | none => "absent"
    | some fn =>
      s!"{fn.name} {fn.inputs.keys} : {(Std.format fn.output).pretty}"

/-- info: simplifyTestStateOnly [n] : int -/
#guard_msgs in
#eval IO.println accumulatedFactoryReaches

/-! ### A definition read only by a loop invariant survives

An invariant is a read like the measure and the guard, so the definition it names is
live. This is the invariant counterpart to `measureKeepsAlive`. -/

private def invariantKeepsAlive :=
#strata
program Core;
procedure p (n : int)
{
  var bound : int := int.add(n, 1);
  var i : int := 0;
  while (int.lt(i, n))
    invariant int.le(i, bound)
  {
    i := int.add(i, 1);
  }
};
#end

/-- info: program Core;

procedure p (n : int)
{
  var bound : int := int.add(n, 1);
  var i : int := 0;
  while (int.lt(i, n))
  invariant int.le(i, bound)
  {
    i := int.add(i, 1);
  }
}; -/
#guard_msgs in
#eval simplifyAndPrint invariantKeepsAlive

/-! ### A dead definition inside a branch is dropped

The sweep recurses into branches, so a definition an arm no longer reads goes even
though the arm itself stays. -/

private def deadInsideBranch :=
#strata
program Core;
function g (x : int) : int;
procedure p (x : int)
{
  if (int.gt(g(x), 0)) {
    var inner : int := 5;
    assert [live]: int.ge(inner, 0);
  }
};
#end

/-- info: program Core;

function g (x : int) : int;
procedure p (x : int)
{
  if (int.gt(g(x), 0)) {
    assert [live]: true;
  }
}; -/
#guard_msgs in
#eval simplifyAndPrint deadInsideBranch

/-! ### The sweep reaches a definition nested two branches deep

The branch counterpart of `deadInsideNestedLoop`. Opaque guards keep both branches
undecided, since a decided one would collapse the nesting before the sweep runs. -/

private def deadInsideNestedBranch :=
#strata
program Core;
function g (x : int) : int;
procedure p (x : int)
{
  if (int.gt(g(x), 0)) {
    if (int.gt(g(int.add(x, 1)), 0)) {
      var inner : int := 5;
      assert [live]: int.ge(inner, 0);
    }
  }
};
#end

/-- info: program Core;

function g (x : int) : int;
procedure p (x : int)
{
  if (int.gt(g(x), 0)) {
    if (int.gt(g(int.add(x, 1)), 0)) {
      assert [live]: true;
    }
  }
}; -/
#guard_msgs in
#eval simplifyAndPrint deadInsideNestedBranch

/-! ### A chain of dead definitions that may not evaluate is kept

Each value here is multi-node and would grow at its use, so none is substituted away,
and nothing reads `c`, `b` or `a` once `c` is gone. The sweep still keeps all three: it
drops an `init` only when its right-hand side surely evaluates (`surelyEvaluates`),
because dropping a step the original program might get stuck on would give the pruned
program runs the original does not have. An `int.add` of a variable may get stuck. -/

private def deadChain :=
#strata
program Core;
procedure p (x : int)
{
  var a : int := int.add(x, 1);
  var b : int := int.add(a, a);
  var c : int := int.add(b, b);
  assert [readsNone]: int.ge(x, 0);
};
#end

/-- info: program Core;

procedure p (x : int)
{
  var a : int := int.add(x, 1);
  var b : int := int.add(a, a);
  var c : int := int.add(b, b);
  assert [readsNone]: int.ge(x, 0);
}; -/
#guard_msgs in
#eval simplifyAndPrint deadChain

/-! ### A dead copy or constructor is dropped, a dead operation is kept

`surelyEvaluates` accepts the right-hand side of `z`, a copy of the parameter `y`, which
the body never writes, of `w`, a copy of `z`, which is defined before it, and of `o`, a
nullary constructor, so the sweep drops all three. It rejects `real.add(a, b)` and the
tester `Opt..isNone(q)` on the symbolic `q`, either of which may get stuck, so it keeps
`t` and `s` although nothing reads them. -/

private def deadCopyAndConstructor :=
#strata
program Core;

datatype Opt () { None(), Some(v: int) };

procedure p (y : int, a : real, b : real, q : Opt)
{
  var z : int := y;
  var w : int := z;
  var o : Opt := None();
  var t : real := real.add(a, b);
  var s : bool := Opt..isNone(q);
  assert [ok]: int.ge(y, 0);
};
#end

/-- info: program Core;

datatype Opt {
  None(),
  Some(v : int)
};
procedure p (y : int, a : real, b : real, q : Opt)
{
  var t : real := real.add(a, b);
  var s : bool := Opt..isNone(q);
  assert [ok]: int.ge(y, 0);
}; -/
#guard_msgs in
#eval simplifyAndPrint deadCopyAndConstructor

/-! ### A size-neutral substitution still lets the next round work

`dup(a)` declines expansion while `a` is symbolic. Substituting `a` gives `dup(3)`, no
smaller, and the second expansion pass reduces it. -/

private def substThenExpand :=
#strata
program Core;

inline function dup (v : int) : int { int.add(v, v) }

procedure p (x : int)
{
  var a : int := 3;
  var r : int := dup(a);
  assert [ok]: int.ge(r, 0);
};
#end

/-- info: program Core;

inline function dup (v : int) : int {
  int.add(v, v)
}
procedure p (x : int)
{
  assert [ok]: true;
}; -/
#guard_msgs in
#eval simplifyAndPrint substThenExpand

/-- info: true -/
#guard_msgs in
#eval IO.println s!"{idempotent substThenExpand}"

/-! ### A value both arms agree on survives the branch; a disagreement does not

Which arm ran is not decided here, so a variable is still known afterwards only when
both arms leave it holding the same value. -/

private def branchAgrees :=
#strata
program Core;
function g (x : int) : int;
procedure p (x : int)
{
  var a : int := 0;
  if (int.gt(g(x), 0)) {
    a := 5;
  } else {
    a := 5;
  }
  assert [agreed]: int.ge(a, 0);
};
#end

/-- info: program Core;

function g (x : int) : int;
procedure p (x : int)
{
  var a : int := 0;
  if (int.gt(g(x), 0)) {
    a := 5;
  } else {
    a := 5;
  }
  assert [agreed]: true;
}; -/
#guard_msgs in
#eval simplifyAndPrint branchAgrees

private def branchDisagrees :=
#strata
program Core;
function g (x : int) : int;
procedure p (x : int)
{
  var a : int := 0;
  if (int.gt(g(x), 0)) {
    a := 5;
  } else {
    a := 6;
  }
  assert [disagreed]: int.ge(a, 0);
};
#end

/-- info: program Core;

function g (x : int) : int;
procedure p (x : int)
{
  var a : int := 0;
  if (int.gt(g(x), 0)) {
    a := 5;
  } else {
    a := 6;
  }
  assert [disagreed]: int.ge(a, 0);
}; -/
#guard_msgs in
#eval simplifyAndPrint branchDisagrees

/-! ### A call to a function with a precondition is never expanded

The obligation a precondition generates exists because the call does, so expanding the
call away would leave the precondition unchecked and unreported. `halve` mentions its
parameter once, so the shape rule alone would admit it; the precondition is what
declines it, and the call survives. -/

private def precondNotExpanded :=
#strata
program Core;

inline function halve (v : int) : int
  requires int.ge(v, 0);
{ int.div(v, 2) }

procedure p (x : int)
{
  var r : int := halve(x);
  assert [ok]: int.ge(r, 0);
};
#end

/-- info: program Core;

inline function halve (v : int) : int requires int.ge(v, 0);
   {
  int.div(v, 2)
}
procedure p (x : int)
{
  var r : int := halve(x);
  assert [ok]: int.ge(r, 0);
}; -/
#guard_msgs in
#eval simplifyAndPrint precondNotExpanded

/-! ### An agreed value that mentions an arm-local is not recorded

Both arms leave `a` holding the same value, but that value is an arm-local name which
leaves scope at the join, so recording it would carry a dangling reference past the
branch. Agreement on the value is not sufficient; the value has to be in scope after
the branch as well. -/

private def branchAgreesArmLocal :=
#strata
program Core;
function g (x : int) : int;
procedure p (x : int)
{
  var a : int := 0;
  if (int.gt(g(x), 0)) {
    var t : int := int.add(x, 1);
    a := t;
  } else {
    var t : int := int.add(x, 1);
    a := t;
  }
  assert [notRecorded]: int.ge(a, 0);
};
#end

/-- info: program Core;

function g (x : int) : int;
procedure p (x : int)
{
  var a : int := 0;
  if (int.gt(g(x), 0)) {
    var t : int := int.add(x, 1);
    a := t;
  } else {
    var t : int := int.add(x, 1);
    a := t;
  }
  assert [notRecorded]: int.ge(a, 0);
}; -/
#guard_msgs in
#eval simplifyAndPrint branchAgreesArmLocal


/-! ### Nested expansion stops at the expansion budget

Each expansion that exposes another call spends one unit of `expandFuel`, and
`simplifyExpr` makes two passes. A chain of ten single-use inline functions is
therefore expanded only partly: the call left over reaches symbolic evaluation, which
sees it as `inlineIfAllValues` on a symbolic argument and keeps it. -/

private def inlineChain :=
#strata
program Core;

inline function f1 (v : int) : int { int.add(v, 1) }
inline function f2 (v : int) : int { f1(v) }
inline function f3 (v : int) : int { f2(v) }
inline function f4 (v : int) : int { f3(v) }
inline function f5 (v : int) : int { f4(v) }
inline function f6 (v : int) : int { f5(v) }
inline function f7 (v : int) : int { f6(v) }
inline function f8 (v : int) : int { f7(v) }
inline function f9 (v : int) : int { f8(v) }
inline function f10 (v : int) : int { f9(v) }

procedure p (x : int)
{
  assert [c]: int.ge(f10(x), 0);
};
#end

/-- info: program Core;

inline function f1 (v : int) : int {
  int.add(v, 1)
}
inline function f2 (v : int) : int {
  f1(v)
}
inline function f3 (v : int) : int {
  f2(v)
}
inline function f4 (v : int) : int {
  f3(v)
}
inline function f5 (v : int) : int {
  f4(v)
}
inline function f6 (v : int) : int {
  f5(v)
}
inline function f7 (v : int) : int {
  f6(v)
}
inline function f8 (v : int) : int {
  f7(v)
}
inline function f9 (v : int) : int {
  f8(v)
}
inline function f10 (v : int) : int {
  f9(v)
}
procedure p (x : int)
{
  assert [c]: int.ge(f2(x), 0);
}; -/
#guard_msgs in
#eval simplifyAndPrint inlineChain


/-! ### A lemma is simplified under its outer quantifiers

`simplifyExpr` does not descend under a binder, so the phase opens a lemma's outer
`forall`s, simplifies the body, and binds the variables again. Here `dup(3)` folds to `6`
and `dup` on the bound `x` expands, its argument being a single node. -/

private def lemmaBody :=
#strata
program Core;

inline function dup (v : int) : int { int.add(v, v) }

lemma [six]: forall x : int :: dup(3) == int.add(dup(x), int.sub(6, dup(x)));
#end

/-- info: program Core;

inline function dup (v : int) : int {
  int.add(v, v)
}
lemma [six] (x : int): 6 == int.add(int.add(x, x), int.sub(6, int.add(x, x))); -/
#guard_msgs in
#eval simplifyAndPrint lemmaBody


/-! ## A function that had preconditions

`precondElim` strips a function's preconditions from its declaration, but registers the
original, preconditions included, in the transform factory. The phase reads the
program's declaration, so it expands `half(y)` into `int.div(y, 2)`. -/

private def precondFn :=
#strata
program Core;

inline function half (v : int) : int
  requires int.ge(v, 0);
{ int.div(v, 2) }

procedure P (y : int) {
  assume int.ge(y, 0);
  assert [h]: int.le(half(y), y);
};
#end

/-- Run `precondElim`, then this phase, and print the program. -/
private def precondElimThenSimplify (p : StrataDDM.Program) : IO Unit :=
  match Core.Transform.run (translateCore p) (fun q => do
      let (_, q) ← _root_.Core.PrecondElim.precondElim q
      Core.Simplify.runSimplify q)
      { Core.Transform.CoreTransformState.emp with factory := Core.Factory } with
  | .error e => IO.println s!"failed: {e}"
  | .ok (_, q) =>
    let s := (Core.formatProgram q).pretty
    IO.print (s.toList.reverse.dropWhile (· == '\n') |>.reverse |> String.ofList)

/-- info: program Core;

inline function half (v : int) : int {
  int.div(v, 2)
}
procedure P (y : int)
{
  assume [assume_0]: int.ge(y, 0);
  assert [assert_h_calls_half_0]: int.ge(y, 0);
  assert [h]: int.le(int.div(y, 2), y);
}; -/
#guard_msgs in
#eval precondElimThenSimplify precondFn


end Core.Simplify.Tests
