/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section

/-! # Equality simplification

The `equalitySimplification` phase substitutes into each `assert` and `cover`
goal the values that ground axioms, `assume`s and definitions give its terms,
and folds the result. A goal that becomes `true` is proved, and a `cover` whose
goal becomes `false` is unreachable, without a solver.

Each test verifies a program with the phase added after `simplify` in the
default order, under a discharge that proves every query it receives and counts
them: a goal the phase decides never reaches it. -/

namespace Strata.EqualitySimplificationTest

private def parse (p : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

/-- The default order with the phase after `simplify`, or the default order itself. -/
private def pipelineWith (phase : Bool) (after : String := "simplify")
    (foldAxioms : Bool := false) : IO (Core.ValidatedPipeline Core.ProgramFactSet.empty) :=
  -- Built from the options the tests verify with, so type checking stays quiet.
  let base := Core.corePipelinePhases .quiet
  let extra := (if foldAxioms then [Strata.Core.passFoldAxioms] else []) ++
    (if phase then [Strata.Core.passEqualitySimplification] else [])
  let phases := (Strata.Core.splicePhasesAfter after extra base).toOption.getD base
  match Strata.Core.validatePipeline phases with
  | .ok vp => pure vp
  | .error e => throw (IO.userError e)

/-- Verify `p` with a counting discharge, then print each obligation's verdict
    and how many queries reached the discharge. -/
private def countedDischarge (p : StrataDDM.Program) (phase : Bool := true)
    (after : String := "simplify") (foldAxioms : Bool := false)
    (options : Core.VerifyOptions := .quiet) : IO Unit := do
  let calls ← IO.mkRef (0 : Nat)
  let mk : Core.MkDischargeFn := fun _ _ _ _ _ _ _ _ _ =>
    fun _ _ _ _ _ _ _ => do
      calls.modify (· + 1)
      pure (.ok (.unsat, .unsat, Strata.SMT.EncoderState.init))
  match ← (Strata.Core.verifyProgram (parse p) options
      (pipeline := some (← pipelineWith phase after foldAxioms)) (mkDischarge := mk)).toBaseIO with
  | .ok results =>
    for r in results do
      let verdict := if r.isSuccess then "pass" else "fail"
      IO.println s!"{r.obligation.label}: {verdict}"
    IO.println s!"discharge calls: {← calls.get}"
  | .error e => IO.println s!"error: {e}"

/-! ## Equality to a literal -/

private def literalPgm :=
#strata
program Core;
procedure P(n : int, s : string)
{
  assume n == 3;
  assume s == "ab";
  assert [intFolds]: int.gt(int.add(n, 1), 3);
  assert [stringFolds]: str.len(str.concat(s, "c")) == 3;
};
#end

/--
info: intFolds: pass
stringFolds: pass
discharge calls: 0
-/
#guard_msgs in
#eval countedDischarge literalPgm

/-! ## Equality to a constructor application, with selectors and testers -/

private def constructorPgm :=
#strata
program Core;
datatype Option () { None(), Some(val: int) };
procedure P(x : Option, y : int)
{
  assume x == Some(y);
  assert [tester]: Option..isSome(x) && !Option..isNone(x);
  assert [selector]: Option..val(x) == y;
};
#end

-- The selector's precondition, that `x` is a `Some`, is decided too.
/--
info: tester: pass
assert_selector_calls_Option..val_0: pass
selector: pass
discharge calls: 0
-/
#guard_msgs in
#eval countedDischarge constructorPgm

/-! ## A function application with a recorded value -/

private def applicationPgm :=
#strata
program Core;
function f(n : int) : int;
procedure P(y : int)
{
  assume f(y) == 5;
  assert [application]: int.gt(f(y), 3);
};
#end

/--
info: application: pass
discharge calls: 0
-/
#guard_msgs in
#eval countedDischarge applicationPgm

/-! ## Boolean facts, negations and conjunctions -/

private def booleanPgm :=
#strata
program Core;
procedure P(b : bool, c : bool)
{
  assume b && !c;
  assert [booleans]: (b || c) && !(b && c);
};
#end

/--
info: booleans: pass
discharge calls: 0
-/
#guard_msgs in
#eval countedDischarge booleanPgm

/-! ## A cover the facts make unreachable

The goal becomes `false`, so the cover and its path condition are unsatisfiable
together, which fails the cover. -/

private def coverPgm :=
#strata
program Core;
datatype Option () { None(), Some(val: int) };
procedure P(x : Option)
{
  assume x == Some(3);
  cover [unreachable]: x == None();
};
#end

/--
info: unreachable: fail
discharge calls: 0
-/
#guard_msgs in
#eval countedDischarge coverPgm

/-! ## Goals the facts do not settle

Arithmetic folds only on literals, and a failing goal still needs the solver to
tell whether its path is reachable. -/

private def residualPgm :=
#strata
program Core;
function f(n : int) : int;
procedure P(y : int)
{
  assume f(y) == 5;
  assert [symbolic]: int.gt(int.add(f(y), y), y);
  assert [refuted]: f(y) == 4;
};
#end

/--
info: symbolic: pass
refuted: pass
discharge calls: 2
-/
#guard_msgs in
#eval countedDischarge residualPgm

/-! ## Without the phase

In the default order, which does not list the phase, every goal above reaches the solver. -/

/--
info: tester: pass
assert_selector_calls_Option..val_0: pass
selector: pass
discharge calls: 3
-/
#guard_msgs in
#eval countedDischarge constructorPgm (phase := false)

/-! ## Facts the phase does not use

A variable or term given two different values is left alone; a fact learned in
a branch does not hold after it; a write drops the facts about the variable.
The two conflicting values in `Conflicts` make its later goals vacuously valid,
which the solver confirms below; once `assume x == 2` folds to `false` under
`x == 1`, the phase leaves every later goal to it rather than deciding it from an
inconsistent path. `Scopes` has no conflicting facts, so its goals after the
branch and the havoc fail with the solver, and would pass if the phase kept a
fact it should drop. -/

private def unusedPgm :=
#strata
program Core;
function f(n : int) : int;
procedure Conflicts(x : int)
{
  assume x == 1;
  assume x == 2;
  assert [twoValues]: x == 1;
  assume f(1) == 1;
  assume f(1) == 2;
  assert [twoTermValues]: f(1) == 1;
};
procedure Scopes(c : bool)
{
  var n : int;
  if (c) {
    assume n == 3;
    assert [inBranch]: int.gt(n, 2);
  }
  assert [afterBranch]: int.gt(n, 2);
  assume n == 3;
  havoc n;
  assert [afterHavoc]: n == 3;
};
#end

/--
info: twoValues: pass
twoTermValues: pass
inBranch: pass
afterBranch: pass
afterHavoc: pass
discharge calls: 4
-/
#guard_msgs in
#eval countedDischarge unusedPgm

/-! ## A pinned term that appears only once the goal is folded

The fact pins `g(t)`, but the goal mentions `g(Option..val(Some(t)))`, which is
`g(t)` only after the selector reduces. The phase folds the goal before
substituting, so it still decides it. Placed right after type checking, before
`simplify` would fold the selector itself. -/

private def foldFirstPgm :=
#strata
program Core;
datatype Option () { None(), Some(val: int) };
function g(n : int) : int;
procedure P(t : int)
{
  assume g(t) == 3;
  assert [foldFirst]: int.gt(g(Option..val(Some(t))), 2);
};
#end

/--
info: assert_foldFirst_calls_Option..val_0: pass
foldFirst: pass
discharge calls: 0
-/
#guard_msgs in
#eval countedDischarge foldFirstPgm (after := "typeCheck")

/-! ## An axiom whose value appears once it is folded

`g(0) == Box..w(box())` gives no fact as written: neither side is a value or a
constructor application. `foldAxioms` expands the inline `box()` and reduces the
selector, giving `g(0) == 5`, which the phase then reads. Without `foldAxioms`
the goal reaches the solver. -/

private def foldAxiomsPgm :=
#strata
program Core;
datatype Box () { MkBox(w: int) };
function g(n : int) : int;
inline function box() : Box { MkBox(5) }
axiom [gBox]: g(0) == Box..w(box());
procedure P()
{
  assert [fromFoldedAxiom]: int.gt(g(0), 4);
};
#end

/--
info: fromFoldedAxiom: pass
discharge calls: 0
fromFoldedAxiom: pass
discharge calls: 1
-/
#guard_msgs in
#eval do
  countedDischarge foldAxiomsPgm (foldAxioms := true)
  countedDischarge foldAxiomsPgm

/-! ## A ground axiom -/

private def axiomPgm :=
#strata
program Core;
function f(n : int) : int;
axiom [fZero]: f(0) == 5;
procedure P()
{
  assert [fromAxiom]: int.gt(f(0), 3);
};
#end

/--
info: fromAxiom: pass
discharge calls: 0
-/
#guard_msgs in
#eval countedDischarge axiomPgm

/-! ## A long conjunction

Bounded-quantifier unrolling produces right-nested conjunctions such as this
axiom's. Every conjunct gives a fact, however deep, so the last one decides the
goal. -/

private def conjunctionPgm :=
#strata
program Core;
const x0 : int;
const x1 : int;
const x2 : int;
const x3 : int;
const x4 : int;
const x5 : int;
const x6 : int;
const x7 : int;
const x8 : int;
const x9 : int;
const x10 : int;
const x11 : int;
const x12 : int;
const x13 : int;
const x14 : int;
const x15 : int;
const x16 : int;
const x17 : int;
const x18 : int;
const x19 : int;
const x20 : int;
axiom [many]: x0 == 0 && (x1 == 1 && (x2 == 2 && (x3 == 3 && (x4 == 4 && (x5 == 5 && (x6 == 6 && (x7 == 7 && (x8 == 8 && (x9 == 9 && (x10 == 10 && (x11 == 11 && (x12 == 12 && (x13 == 13 && (x14 == 14 && (x15 == 15 && (x16 == 16 && (x17 == 17 && (x18 == 18 && (x19 == 19 && (x20 == 20))))))))))))))))))));
procedure P()
{
  assert [lastConjunct]: x20 == 20;
};
#end

/--
info: lastConjunct: pass
discharge calls: 0
-/
#guard_msgs in
#eval countedDischarge conjunctionPgm

/-! ## Definitions

A definition `var y : T := e` is a fact about `y`. A goal reads a defined variable
through its definition (`expanded`, which symbolic evaluation also decides), an
assumption does too, both to orient an equality (`oriented`) and when it is a
boolean variable (`boolDef`), and a write to a variable the definition mentions
drops it (`defDropped`, which reaches the solver). The same program without the
phase shows which goals the phase decides. -/

private def definitionPgm :=
#strata
program Core;
datatype Option () { None(), Some(val: int) };
procedure Expand()
{
  var y : Option := Some(3);
  assert [expanded]: Option..val(y) == 3;
};
procedure Orient(x : Option)
{
  var y : Option := Some(3);
  assume x == y;
  assert [oriented]: Option..isSome(x);
};
procedure Written()
{
  var n : int;
  var y : int := n;
  n := 5;
  assert [defDropped]: y == 5;
};
procedure BoolDef(x : int)
{
  var b : bool := x == 1;
  assume b;
  assert [boolDef]: x == 1;
};
#end

/--
info: assert_expanded_calls_Option..val_0: pass
expanded: pass
oriented: pass
defDropped: pass
boolDef: pass
discharge calls: 1
assert_expanded_calls_Option..val_0: pass
expanded: pass
oriented: pass
defDropped: pass
boolDef: pass
discharge calls: 3
-/
#guard_msgs in
#eval do
  countedDischarge definitionPgm
  countedDischarge definitionPgm (phase := false)

/-! ## A definition that reads the variable it shadows

Inside the branch, `l := Cons(1, l)` would read the parameter `l` and define a new
`l`; read as a definition of itself, it would unfold `l` into `Cons(1, Cons(1, …))`.
The type checker rejects such a declaration, and the phase, which does not record a
definition that mentions its own variable, does not rely on it. -/

private def shadowDefPgm :=
#strata
program Core;
datatype L () { Nil(), Cons(hd: int, tl: L) };
procedure P(l : L, c : bool)
{
  if (c) {
    var l : L := Cons(1, l);
    assert [shadowed]: L..isCons(L..tl(l));
  }
};
#end

/-- info: rejected as shadowing: true -/
#guard_msgs in
#eval show IO Unit from do
  let r ← (Strata.Core.verifyProgram (parse shadowDefPgm) .quiet).toBaseIO
  match r with
  | .error e =>
    let shadowing := decide ((s!"{e}".splitOn "already in context").length > 1)
    IO.println s!"rejected as shadowing: {shadowing}"
  | .ok _ => IO.println "accepted"

/-! ## An equality between two opaque terms

Neither side of `f(a) == g(b)` is a value, so neither replaces the other, but the
equality itself is a fact. -/

private def opaqueEqPgm :=
#strata
program Core;
function f(n : int) : int;
function g(n : int) : int;
procedure P(a : int, b : int)
{
  assume f(a) == g(b);
  assert [sameEquality]: f(a) == g(b);
};
#end

/--
info: sameEquality: pass
discharge calls: 0
-/
#guard_msgs in
#eval countedDischarge opaqueEqPgm

/-! ## A chain of definitions

An equality is oriented by reading up to `defDepth` definitions: `d15` is read back
to `Some(3)`, but `d16` is one definition too deep, so `beyondDepth` reaches the
solver. Placed right after type checking, before `simplify` would shorten the chain.
Without the phase both goals reach the solver. -/

private def depthPgm :=
#strata
program Core;
datatype Option () { None(), Some(val: int) };
procedure Chain(x : Option, z : Option)
{
  var d0 : Option := Some(3);
  var d1 : Option := d0;
  var d2 : Option := d1;
  var d3 : Option := d2;
  var d4 : Option := d3;
  var d5 : Option := d4;
  var d6 : Option := d5;
  var d7 : Option := d6;
  var d8 : Option := d7;
  var d9 : Option := d8;
  var d10 : Option := d9;
  var d11 : Option := d10;
  var d12 : Option := d11;
  var d13 : Option := d12;
  var d14 : Option := d13;
  var d15 : Option := d14;
  var d16 : Option := d15;
  assume x == d15;
  assume z == d16;
  assert [withinDepth]: Option..isSome(x);
  assert [beyondDepth]: Option..isSome(z);
};
#end

/--
info: withinDepth: pass
beyondDepth: pass
discharge calls: 1
withinDepth: pass
beyondDepth: pass
discharge calls: 2
-/
#guard_msgs in
#eval do
  countedDischarge depthPgm (after := "typeCheck")
  countedDischarge depthPgm (after := "typeCheck") (phase := false)

/-! ## A parameter named like an axiom's variable

The axiom constrains the constant `g`; the parameter `g` of `P` is another
name, so the phase must not rewrite it with the axiom's value: the goal
reaches the solver. -/

private def shadowPgm :=
#strata
program Core;
const g : int;
axiom [gOne]: g == 1;
procedure P(g : int)
{
  assert [paramNotGlobal]: g == 1;
};
#end

/--
info: paramNotGlobal: pass
discharge calls: 1
-/
#guard_msgs in
#eval countedDischarge shadowPgm

/-! ## An axiom declared after the procedure

Obligation extraction gives a procedure only the axioms declared before it, so the
phase must not use `cOne` in `P`: the goal reaches the solver. -/

private def axiomAfterPgm :=
#strata
program Core;
const c : int;
procedure P()
{
  assert [cIsOne]: c == 1;
};
axiom [cOne]: c == 1;
#end

/--
info: cIsOne: pass
discharge calls: 1
-/
#guard_msgs in
#eval countedDischarge axiomAfterPgm

/-! ## Contradictory assumptions

After `assume x == 1; assume !(x == 1)` the facts would fold the goal `x == 1` to
`false`, a value their inconsistency produced. The phase leaves goals on such a path
alone, so under `deductiveAssumingSatisfiablePaths`, which reports a goal folded to
`false` as failing, the goal still reaches the solver, which finds it vacuously valid.
The same holds when the contradiction appears only once the facts are substituted,
as in `x == y` under `x == 1` and `y == 2`. -/

private def contradictionPgm :=
#strata
program Core;
procedure P(x : int)
{
  assume x == 1;
  assume !(x == 1);
  assert [vacuous]: x == 1;
};
procedure Q(x : int, y : int)
{
  assume x == 1;
  assume y == 2;
  assume x == y;
  assert [vacuousBySubstitution]: x == 2;
};
#end

/--
info: vacuous: pass
vacuousBySubstitution: pass
discharge calls: 2
-/
#guard_msgs in
#eval countedDischarge contradictionPgm
  (options := { Core.VerifyOptions.quiet with checkMode := .deductiveAssumingSatisfiablePaths })

/-! ## Agreement with the solver

Every program above, verified with the solver three times: without the phases,
with `equalitySimplification`, and with `foldAxioms` before it. Each obligation
gets the same verdict in the three runs, both in deductive mode and in
`deductiveAssumingSatisfiablePaths`, the mode in which a goal folded to `false` is
reported failing without a solver. -/

/-- Verify `p` with the solver under `checkMode`, without the phases, with
    `equalitySimplification`, and with `foldAxioms` before it, and print each
    obligation's verdict when the three runs agree, or every verdict when they do
    not. -/
private def agreesWithSolver (checkMode : Core.VerificationMode) (p : StrataDDM.Program)
    (after : String := "simplify") : IO Unit := do
  let options := { Core.VerifyOptions.quiet with checkMode }
  let run (phase foldAxioms : Bool) : IO _ := do
    let vp ← pipelineWith phase after foldAxioms
    (Strata.Core.verifyProgram (parse p) options (pipeline := some vp)).toBaseIO
  let verdict (r : Core.VCResult) : String :=
    let v := if r.isSuccess then "pass" else if r.isFailure then "fail" else "other"
    s!"{r.obligation.label}: {v}"
  match ← run false false, ← run true false, ← run true true with
  | .ok off, .ok on, .ok folded =>
    if on.size != off.size || folded.size != off.size then
      IO.println "DISAGREE on the number of obligations"
    for ((a, b), c) in (off.toList.zip on.toList).zip folded.toList do
      if verdict a == verdict b && verdict a == verdict c then IO.println (verdict a)
      else IO.println s!"DISAGREE {verdict a} / {verdict b} / {verdict c}"
  | .error e, _, _ | _, .error e, _ | _, _, .error e => IO.println s!"error: {e}"

/-- Every program above, verified by `agreesWithSolver` under `checkMode`. -/
private def allAgreeWithSolver (checkMode : Core.VerificationMode) : IO Unit := do
  for p in [literalPgm, constructorPgm, applicationPgm, booleanPgm, coverPgm, residualPgm,
      unusedPgm, foldAxiomsPgm, axiomPgm, conjunctionPgm, definitionPgm, shadowPgm,
      axiomAfterPgm, contradictionPgm, opaqueEqPgm] do
    agreesWithSolver checkMode p
  agreesWithSolver checkMode foldFirstPgm (after := "typeCheck")
  agreesWithSolver checkMode depthPgm (after := "typeCheck")

/--
info: intFolds: pass
stringFolds: pass
tester: pass
assert_selector_calls_Option..val_0: pass
selector: pass
application: pass
booleans: pass
unreachable: fail
symbolic: pass
refuted: fail
twoValues: pass
twoTermValues: pass
inBranch: pass
afterBranch: fail
afterHavoc: fail
fromFoldedAxiom: pass
fromAxiom: pass
lastConjunct: pass
assert_expanded_calls_Option..val_0: pass
expanded: pass
oriented: pass
defDropped: fail
boolDef: pass
paramNotGlobal: fail
cIsOne: fail
vacuous: pass
vacuousBySubstitution: pass
sameEquality: pass
assert_foldFirst_calls_Option..val_0: pass
foldFirst: pass
withinDepth: pass
beyondDepth: pass
-/
#guard_msgs in
#eval allAgreeWithSolver .deductive

/--
info: intFolds: pass
stringFolds: pass
tester: pass
assert_selector_calls_Option..val_0: pass
selector: pass
application: pass
booleans: pass
unreachable: fail


Obligation refuted: failed!

Result obtained during evaluation.


Obligation refuted: failed!

Result obtained during evaluation.
symbolic: pass
refuted: fail
twoValues: pass
twoTermValues: pass
inBranch: pass
afterBranch: fail
afterHavoc: fail
fromFoldedAxiom: pass
fromAxiom: pass
lastConjunct: pass
assert_expanded_calls_Option..val_0: pass
expanded: pass
oriented: pass
defDropped: fail
boolDef: pass
paramNotGlobal: fail
cIsOne: fail
vacuous: pass
vacuousBySubstitution: pass
sameEquality: pass
assert_foldFirst_calls_Option..val_0: pass
foldFirst: pass
withinDepth: pass
beyondDepth: pass
-/
#guard_msgs in
#eval allAgreeWithSolver .deductiveAssumingSatisfiablePaths

end Strata.EqualitySimplificationTest

end
