/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Transform.EqualitySimplification
meta import StrataTest.Transform.EqualitySimplificationGoalsDefined
import StrataDDM.Integration.Lean.HashCommands

meta section

/-! # Equality simplification

The `equalitySimplification` phase substitutes into each `assert`, `cover` and
lemma goal the values that ground axioms, `assume`s and definitions give its
terms, and folds the result. A goal that becomes `true` is proved, and a
`cover` whose goal becomes `false` is unreachable, without a solver.

Most tests verify a program with the phase added after `simplify` in the
default order, under a discharge that proves every query it receives and counts
them: a goal the phase decides never reaches it. Most tests from the lemma
section on print the program after the phase alone, and an agreement block at
the end of each section verifies them with the solver. -/

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

/-- The body of `literalPgm`, as type checking leaves it, is the one
    `Core.EqualitySimplification.GoalsDefinedTest.literal_goalsDefined` proves has goals with
    values. -/
private def literalBodyExprs : Option (List Core.Expression.Expr) := do
  let p ← (Core.typeCheck .quiet (parse literalPgm)).toOption
  let q ← p.decls.findSome? fun | .proc q _ => some q | _ => none
  let .structured ss := q.body | none
  ss.mapM fun
    | .cmd (.cmd (.assume _ e _)) | .cmd (.cmd (.assert _ e _)) => some e
    | _ => none

open Core.EqualitySimplification.GoalsDefinedTest in
#guard literalBodyExprs ==
  some [.eq () n (.intConst () 3), .eq () s (.strConst () "ab"), intGoal, strGoal]

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

/-! A contradiction in an assumption that gives no fact is missed: the goal
folds to `false` and, under `deductiveAssumingSatisfiablePaths`, fails without
a solver call. -/

private def unseenContradictionPgm :=
#strata
program Core;
procedure P()
{
  assume forall x : int :: int.lt(x, x);
  assert [unseenContradiction]: str.in.re("b", re.*(str.to.re("a")));
};
#end

/--
info:

Obligation unseenContradiction: failed!

Result obtained during evaluation.
unseenContradiction: fail
discharge calls: 0
-/
#guard_msgs in
#eval countedDischarge unseenContradictionPgm
  (options := { Core.VerifyOptions.quiet with
    checkMode := .deductiveAssumingSatisfiablePaths })

/-! A contradiction the facts do not expose is not detected, so under
`deductiveAssumingSatisfiablePaths` a goal folded to `false` fails. -/

private def undetectedBvPgm :=
#strata
program Core;
procedure P(x : int, a : bv W32)
{
  assume int.gt(x, 5);
  assume x == 1;
  assert [undetected]: !(bv32.and(a, bv{32}(0)) == bv{32}(0));
};
#end

/--
info: undetected: pass
discharge calls: 1


Obligation undetected: failed!

Result obtained during evaluation.
undetected: fail
discharge calls: 0
-/
#guard_msgs in
#eval do
  countedDischarge undetectedBvPgm
  countedDischarge undetectedBvPgm (options :=
    { Core.VerifyOptions.quiet with
      checkMode := .deductiveAssumingSatisfiablePaths })

/-! Quantified assumptions add no facts, so their contradiction is not
detected and under `deductiveAssumingSatisfiablePaths` the goal fails. -/

private def undetectedQuantPgm :=
#strata
program Core;
function g (y : int) : bool;
procedure U()
{
  assume forall y : int :: g(y);
  assume exists y : int :: !g(y);
  assert [undetectedQuant]: exists y : int :: int.lt(1, 0) && g(y);
};
#end

/--
info: undetectedQuant: pass
discharge calls: 1


Obligation undetectedQuant: failed!

Result obtained during evaluation.
undetectedQuant: fail
discharge calls: 0
-/
#guard_msgs in
#eval do
  countedDischarge undetectedQuantPgm
  countedDischarge undetectedQuantPgm (options :=
    { Core.VerifyOptions.quiet with
      checkMode := .deductiveAssumingSatisfiablePaths })

/-! ## Agreement with the solver

Each program in `allAgreeWithSolver`'s list, verified with the solver three
times: without the phases, with `equalitySimplification`, and with `foldAxioms`
before it. Each obligation gets the same verdict in the three runs, both in
deductive mode and in `deductiveAssumingSatisfiablePaths`, the mode in which a
goal folded to `false` is reported failing without a solver.

The list leaves out `unseenContradictionPgm`, `undetectedBvPgm` and
`undetectedQuantPgm`. Each has a goal on a contradictory path that the phase
does not detect and folds to `false`, so in
`deductiveAssumingSatisfiablePaths` the phase's run fails where the solver
proves the goal. The end of the file checks them in deductive mode. -/

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

/-- Each program in the list, verified by `agreesWithSolver` under
    `checkMode`. -/
private def allAgreeWithSolver (checkMode : Core.VerificationMode) : IO Unit := do
  for p in [literalPgm, constructorPgm, applicationPgm, booleanPgm, coverPgm, residualPgm,
      unusedPgm, foldAxiomsPgm, axiomPgm, conjunctionPgm, definitionPgm, shadowPgm,
      axiomAfterPgm, contradictionPgm, opaqueEqPgm] do
    agreesWithSolver checkMode p
  agreesWithSolver checkMode foldFirstPgm (after := "typeCheck")
  agreesWithSolver checkMode depthPgm (after := "typeCheck")

/-- Every program in `ps`, verified by `agreesWithSolver` in both modes. -/
private def agreeInBothModes (ps : List StrataDDM.Program) : IO Unit := do
  let modes : List Core.VerificationMode :=
    [.deductive, .deductiveAssumingSatisfiablePaths]
  for mode in modes do
    for p in ps do
      agreesWithSolver mode p

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

/-! ## Lemmas

A lemma is rewritten under the ground axioms declared before it, as an `assert`
is. -/

/-- Run the phase alone on `p`, type checked first when `typeCheck` is set, and
    print the result. -/
private def rewriteAndPrint (p : StrataDDM.Program)
    (typeCheck : Bool := false) : IO Unit := do
  let program ← if typeCheck then
      match Core.typeCheck .quiet (parse p) with
      | .ok typed => pure typed
      | .error e => throw (IO.userError s!"{e}")
    else pure (parse p)
  match Core.Transform.run program
      Core.EqualitySimplification.runEqualitySimplification
      { Core.Transform.CoreTransformState.emp with
        factory := Core.Factory } with
  | .error e => IO.println s!"error: {e}"
  | .ok (_, p') =>
    let s := (Core.formatProgram p').pretty
    IO.println (String.ofList (s.toList.reverse.dropWhile (· == '\n')).reverse)

/-! ### A lemma that folds to `true` -/

private def lemmaPgm :=
#strata
program Core;
datatype Option () { None(), Some(val: int) };
function f(n : int) : Option;
axiom [fZero]: f(0) == Some(3);
lemma [lemmaFolds]: Option..isSome(f(0));
#end

/--
info: program Core;

datatype Option {
  None(),
  Some(val : int)
};
function f (n : int) : Option;
axiom [fZero]: f(0) == Some(3);
lemma [lemmaFolds]: true;
-/
#guard_msgs in
#eval rewriteAndPrint lemmaPgm

/--
info: lemmaFolds: pass
discharge calls: 0
-/
#guard_msgs in
#eval countedDischarge lemmaPgm

/-! ### Which facts a lemma sees

A lemma's obligation assumes only the axioms declared before it, so `cBefore`
is left as written and reaches the solver; `cAfter` folds. A lemma gives no
fact, so `dFirst` does not decide `dAgain`. The `assume` in `P` holds only
inside `P`, so `afterProc` is left as written. -/

private def lemmaOrderPgm :=
#strata
program Core;
const c : int;
const d : int;
lemma [cBefore]: c == 1;
axiom [cOne]: c == 1;
lemma [cAfter]: c == 1;
lemma [dFirst]: d == 2;
lemma [dAgain]: d == 2;
const e : int;
procedure P() {
  assume e == 3;
};
lemma [afterProc]: e == 3;
#end

/--
info: program Core;

function c () : int;
function d () : int;
lemma [cBefore]: c == 1;
axiom [cOne]: c == 1;
lemma [cAfter]: true;
lemma [dFirst]: d == 2;
lemma [dAgain]: d == 2;
function e () : int;
procedure P ()
{
  assume [assume_0]: e == 3;
};
lemma [afterProc]: e == 3;
-/
#guard_msgs in
#eval rewriteAndPrint lemmaOrderPgm

/-! ### Contradictory axioms

After `x == 1` and `!(x == 1)`, the lemma `x == 1` would fold to `false`. The
phase leaves it alone, as it leaves the `assert` with the same goal, and the
solver finds both vacuously valid. -/

private def lemmaContradictionPgm :=
#strata
program Core;
const x : int;
axiom [xOne]: x == 1;
axiom [xNotOne]: !(x == 1);
lemma [vacuousLemma]: x == 1;
procedure P()
{
  assert [vacuousAssert]: x == 1;
};
#end

/--
info: program Core;

function x () : int;
axiom [xOne]: x == 1;
axiom [xNotOne]: !(x == 1);
lemma [vacuousLemma]: x == 1;
procedure P ()
{
  assert [vacuousAssert]: x == 1;
};
-/
#guard_msgs in
#eval rewriteAndPrint lemmaContradictionPgm

/-! ### A quantified lemma

Under a binder, a term without the bound variable is replaced as in an
`assert`: `f(0)` becomes `5` in both, and `f(n)` is left alone. -/

private def lemmaQuantPgm :=
#strata
program Core;
function f(n : int) : int;
axiom [fZero]: f(0) == 5;
lemma [quantLemma]: forall n : int :: int.gt(f(n), f(0)) ==> int.gt(f(n), 4);
procedure P()
{
  assert [quantAssert]:
    forall n : int :: int.gt(f(n), f(0)) ==> int.gt(f(n), 4);
};
#end

/--
info: program Core;

function f (n : int) : int;
axiom [fZero]: f(0) == 5;
lemma [quantLemma] (n : int): int.gt(f(n), 5) ==> int.gt(f(n), 4);
procedure P ()
{
  assert [quantAssert]: forall n : int :: int.gt(f(n), 5) ==> int.gt(f(n), 4);
};
-/
#guard_msgs in
#eval rewriteAndPrint lemmaQuantPgm

/-! ### A quantifier is not a value

A closed quantifier is not a value (`LExpr.isValue`), so `b == ∀ …` does not replace `b`:
the `assert` of `b` is kept, while the `assert` of `c`, which `c == true` gives a value,
folds to `true`. -/

private def quantNotValuePgm :=
#strata
program Core;
procedure P(b : bool, c : bool)
{
  assume c == true;
  assume b == (forall n : int :: n == n);
  assert [cValue]: c;
  assert [bQuant]: b;
};
#end

/--
info: program Core;

procedure P (b : bool, c : bool)
{
  assume [assume_0]: c == true;
  assume [assume_1]: b == (forall n : int :: n == n);
  assert [cValue]: true;
  assert [bQuant]: b;
};
-/
#guard_msgs in
#eval rewriteAndPrint quantNotValuePgm

/-! ### Agreement with the solver

Each lemma program above, verified by `agreesWithSolver` in both modes. -/

/--
info: lemmaFolds: pass
cBefore: fail
cAfter: pass
dFirst: fail
dAgain: fail
afterProc: fail
vacuousLemma: pass
vacuousAssert: pass
quantLemma: pass
quantAssert: pass
lemmaFolds: pass
cBefore: fail
cAfter: pass
dFirst: fail
dAgain: fail
afterProc: fail
vacuousLemma: pass
vacuousAssert: pass
quantLemma: pass
quantAssert: pass
-/
#guard_msgs in
#eval agreeInBothModes
  [lemmaPgm, lemmaOrderPgm, lemmaContradictionPgm, lemmaQuantPgm]

/-! ## Folding under quantifiers

Quantifier bodies are folded, and a quantifier whose body does not use its
variable is replaced by its body. -/

/-! Over builtin types, an uninterpreted type and a datatype. -/

private def vacuousQuantPgm :=
#strata
program Core;
type Opaque;
datatype Option () { None(), Some(val: int) };
const c : int;
function hint (a : bv W32) : bool;
axiom [cOne]: c == 1;
lemma [unusedVariables]: (exists a : bv W32 :: { hint(a) } true) &&
  (forall b : int :: c == 1);
lemma [opaqueType]: forall t : Opaque :: c == 1;
lemma [overOption]: exists o : Option :: c == 1;
#end

/--
info: program Core;

type Opaque;
datatype Option {
  None(),
  Some(val : int)
};
function c () : int;
function hint (a : bv W32) : bool;
axiom [cOne]: c == 1;
lemma [unusedVariables]: true;
lemma [opaqueType]: true;
lemma [overOption]: true;
-/
#guard_msgs in
#eval rewriteAndPrint vacuousQuantPgm

/-! The goals of a program with no facts are folded too. -/

private def noFactsQuantPgm :=
#strata
program Core;
lemma [noFacts]: (exists a : int :: true) && (exists b : int :: true);
#end

/--
info: program Core;

lemma [noFacts]: true;
-/
#guard_msgs in
#eval rewriteAndPrint noFactsQuantPgm

/-! Bodies fold under their quantifier; one whose folded body uses its
variable keeps the quantifier and its trigger. -/

private def mixedQuantPgm :=
#strata
program Core;
const c : int;
function g (x : int) : bool;
function h (x : int, y : int) : bool;
axiom [cOne]: c == 1;
lemma [closedConjunct]: exists x : int :: int.lt(1, 0) && g(x);
lemma [keptQuantifier]: forall y : int :: int.add(c, 1) == 3 || g(y);
lemma [withTrigger]: forall x : int :: { g(x) } int.lt(1, 0) || g(x);
lemma [lifted]: forall x : int :: exists y : int :: int.lt(1, 0) || h(x, y);
#end

/--
info: program Core;

function c () : int;
function g (x : int) : bool;
function h (x : int, y : int) : bool;
axiom [cOne]: c == 1;
lemma [closedConjunct]: false;
lemma [keptQuantifier] (y : int): g(y);
lemma [withTrigger] (x : int) { g(x) }
  : g(x);
lemma [lifted] (x : int): exists y : int :: h(x, y);
-/
#guard_msgs in
#eval rewriteAndPrint mixedQuantPgm

/-! Nested and shadowing quantifiers; a quantifier inside an abstraction is
folded too. -/

private def nestedQuantPgm :=
#strata
program Core;
function g (x : int) : bool;
function h (x : int, y : int) : bool;
function holds (k : int -> bool) : bool;
lemma [nested]: forall x : int :: exists y : int :: g(x);
lemma [shadowed]: forall x : int :: exists x : int :: g(x);
lemma [mentionsX]: exists x : int :: g(x);
lemma [mentionsBoth]: forall x : int :: exists y : int :: h(x, y);
lemma [inLambda]:
  holds(fun x : int => exists y : int :: int.lt(1, 0) && g(y));
#end

/--
info: program Core;

function g (x : int) : bool;
function h (x : int, y : int) : bool;
function holds (k : int -> bool) : bool;
lemma [nested] (x : int): g(x);
lemma [shadowed]: exists x : int :: g(x);
lemma [mentionsX]: exists x : int :: g(x);
lemma [mentionsBoth] (x : int): exists y : int :: h(x, y);
lemma [inLambda]: holds(fun x : int => false);
-/
#guard_msgs in
#eval rewriteAndPrint nestedQuantPgm

/-! Quantifiers in other positions and in a definition body. An assumption
that folds to `false` leaves the goals after it alone. -/

private def positionsQuantPgm :=
#strata
program Core;
const c : int;
function g (x : int) : bool;
axiom [cOne]: c == 1;
lemma [inCondition]:
  if (exists x : int :: int.lt(1, 0) && g(x)) then g(1) else g(2);
lemma [inEquality]: (forall x : int :: int.lt(0, 1) || g(x)) == g(0);
procedure P()
{
  assert [vacuous]: exists x : int :: c == 1;
  cover [vacuousCover]: forall x : int :: int.lt(1, 0) && g(x);
  assume exists x : int :: int.lt(1, 0) && g(x);
  assert [afterDead]: exists x : int :: c == 1;
};
procedure D()
{
  var b : bool := exists x : int :: int.lt(1, 0) && g(x);
  assert [fromDef]: b;
};
#end

/--
info: program Core;

function c () : int;
function g (x : int) : bool;
axiom [cOne]: c == 1;
lemma [inCondition]: g(2);
lemma [inEquality]: true == g(0);
procedure P ()
{
  assert [vacuous]: true;
  cover [vacuousCover]: false;
  assume [assume_0]: exists x : int :: int.lt(1, 0) && g(x);
  assert [afterDead]: exists x : int :: c == 1;
};
procedure D ()
{
  var b : bool := exists x : int :: int.lt(1, 0) && g(x);
  assert [fromDef]: false;
};
-/
#guard_msgs in
#eval rewriteAndPrint positionsQuantPgm

/-! ### Agreement with the solver

Each program of this section, verified by `agreesWithSolver` in both modes. -/

/--
info: unusedVariables: pass
opaqueType: pass
overOption: pass
noFacts: pass
closedConjunct: fail
keptQuantifier: fail
withTrigger: fail
lifted: other
nested: fail
shadowed: other
mentionsX: other
mentionsBoth: other
inLambda: other
inCondition: fail
inEquality: fail
vacuous: pass
vacuousCover: fail
afterDead: pass
fromDef: fail
unusedVariables: pass
opaqueType: pass
overOption: pass
noFacts: pass


Obligation closedConjunct: failed!

Result obtained during evaluation.


Obligation closedConjunct: failed!

Result obtained during evaluation.
closedConjunct: fail
keptQuantifier: fail
withTrigger: fail
lifted: other
nested: fail
shadowed: other
mentionsX: other
mentionsBoth: other
inLambda: other


Obligation fromDef: failed!

Result obtained during evaluation.


Obligation fromDef: failed!

Result obtained during evaluation.
inCondition: fail
inEquality: fail
vacuous: pass
vacuousCover: fail
afterDead: pass
fromDef: fail
-/
#guard_msgs in
#eval agreeInBothModes
  [vacuousQuantPgm, noFactsQuantPgm, mixedQuantPgm, nestedQuantPgm,
    positionsQuantPgm]

/-! ## A bitvector `and` with `0` or all ones

The builtin bitvector `and` with `0` is `0`, and with all ones is its other
argument.

Absorption at each width the factory defines, on either side, nested, and
once evaluation exposes the constant; `or`, `xor` and a mask that is not all
ones are left alone. -/

private def absorbPgm :=
#strata
program Core;
procedure P(a : bv W32, b : bv W32)
{
  assert [maskZero]: bv32.and(a, bv{32}(0)) == bv{32}(0);
  assert [zeroFirst]: bv32.and(bv{32}(0), a) == bv{32}(0);
  assert [allOnes]: bv32.and(a, bv{32}(4294967295)) == a;
  assert [allOnesFirst]: bv32.and(bv{32}(4294967295), a) == a;
  assert [nested]: bv32.and(bv32.and(a, bv{32}(0)), b) == bv{32}(0);
  assert [exposed]: bv32.and(a,
    if bv32.and(b, bv{32}(0)) == bv{32}(0) then bv{32}(0) else bv{32}(1))
    == bv{32}(0);
  assert [orZero]: bv32.or(a, bv{32}(0)) == bv{32}(0);
  assert [xorAllOnes]: bv32.xor(a, bv{32}(4294967295)) == a;
};
procedure Q(a1 : bv W1, a8 : bv W8, a16 : bv W16, a64 : bv W64,
    z : bv W128)
{
  assert [width1]: bv1.and(a1, bv{1}(1)) == a1;
  assert [width8]: bv8.and(a8, bv{8}(255)) == a8;
  assert [width16]: bv16.and(a16, bv{16}(65535)) == a16;
  assert [width64]: bv64.and(a64, bv{64}(18446744073709551615)) == a64;
  assert [width128]: bv128.and(z,
    bv{128}(340282366920938463463374607431768211455)) == z;
  assert [notAllOnes]: bv16.and(a16, bv{16}(255)) == a16;
};
#end

/--
info: program Core;

procedure P (a : bv W32, b : bv W32)
{
  assert [maskZero]: true;
  assert [zeroFirst]: true;
  assert [allOnes]: true;
  assert [allOnesFirst]: true;
  assert [nested]: true;
  assert [exposed]: true;
  assert [orZero]: bv32.or(a, bv{32}(0)) == bv{32}(0);
  assert [xorAllOnes]: bv32.xor(a, bv{32}(4294967295)) == a;
};
procedure Q (a1 : bv W1, a8 : bv W8, a16 : bv W16, a64 : bv W64, z : bv W128)
{
  assert [width1]: true;
  assert [width8]: true;
  assert [width16]: true;
  assert [width64]: true;
  assert [width128]: true;
  assert [notAllOnes]: bv16.and(a16, bv{16}(255)) == a16;
};
-/
#guard_msgs in
#eval rewriteAndPrint absorbPgm

/-! No address is outside the CIDR block `0.0.0.0/0`, so that goal folds to
`false`. -/

private def anyAddressPgm :=
#strata
program Core;
datatype CIDR () { CIDR_Cons(network: bv W32, mask: bv W32) };
procedure P(a : bv W32)
{
  assert [outsideAll]:
    !(bv32.and(a, CIDR..mask(CIDR_Cons(bv{32}(0), bv{32}(0))))
      == bv32.and(CIDR..network(CIDR_Cons(bv{32}(0), bv{32}(0))),
                  CIDR..mask(CIDR_Cons(bv{32}(0), bv{32}(0)))));
};
#end

/--
info: program Core;

datatype CIDR {
  CIDR_Cons(network : bv W32, mask : bv W32)
};
procedure P (a : bv W32)
{
  assert [outsideAll]: false;
};
-/
#guard_msgs in
#eval rewriteAndPrint anyAddressPgm

/-! Absorption in other positions, under quantifiers too, whose bodies are
then folded; a trigger is left as written. -/

private def positionsBvPgm :=
#strata
program Core;
const c : bv W32;
function g (x : bv W32) : bool;
lemma [inLemma]: bv32.and(c, bv{32}(0)) == bv{32}(0);
procedure P(a : bv W32)
{
  assert [inCondition]:
    if bv32.and(a, bv{32}(0)) == bv{32}(0) then true else g(a);
  assert [underExists]:
    exists x : bv W32 :: bv32.and(x, bv{32}(0)) == bv{32}(0);
  assert [boundAllOnes]:
    forall x : bv W32 :: bv32.and(x, bv{32}(4294967295)) == x;
  assert [inTrigger]: forall x : bv W32 :: { bv32.and(x, bv{32}(0)) }
    g(bv32.and(x, bv{32}(0))) ==> g(x);
  cover [inCover]: !(bv32.and(a, bv{32}(0)) == bv{32}(0));
  var m : bv W32 := bv32.and(a, bv{32}(0));
  assert [viaDefinition]: m == bv{32}(0);
  assume !(bv32.and(a, bv{32}(0)) == bv{32}(0));
  assert [afterDead]: bv32.and(a, bv{32}(0)) == bv{32}(0);
};
#end

/--
info: program Core;

function c () : bv W32;
function g (x : bv W32) : bool;
lemma [inLemma]: true;
procedure P (a : bv W32)
{
  assert [inCondition]: true;
  assert [underExists]: true;
  assert [boundAllOnes]: true;
  assert [inTrigger]: forall x : (bv W32) ::  { bv32.and(x, bv{32}(0)) }
    g(bv{32}(0)) ==> g(x);
  cover [inCover]: false;
  var m : bv W32 := bv32.and(a, bv{32}(0));
  assert [viaDefinition]: true;
  assume [assume_0]: !(bv32.and(a, bv{32}(0)) == bv{32}(0));
  assert [afterDead]: bv32.and(a, bv{32}(0)) == bv{32}(0);
};
-/
#guard_msgs in
#eval rewriteAndPrint positionsBvPgm

/-! The guard on `concreteEval`: a program function that replaces the
builtin `and` has none, so it is not absorbed. Surface syntax cannot declare
one, so the factory is built here. -/

private def varA : Core.Expression.Expr := .fvar () ⟨"a", ()⟩ none

/-- The builtin `and` at width `n` applied to `a` and `b`. -/
private def bvAndAt (n : Nat) (a b : Core.Expression.Expr) :
    Core.Expression.Expr :=
  let op := toString (Core.CoreOp.bv ⟨n, .And⟩)
  .app () (.app () (.op () ⟨op, ()⟩ none) a) b

private def andZero : Core.Expression.Expr :=
  bvAndAt 32 varA (.const () (.bitvecConst 32 0))

private def shadowedAnd : Lambda.Factory Core.CoreLParams :=
  Lambda.Factory.ofArray (Core.Factory.toArray.map fun fn =>
    if fn.name.name == toString (Core.CoreOp.bv ⟨32, .And⟩) then
      { fn with concreteEval := none }
    else fn)

#guard Core.EqualitySimplification.bvAndRule Core.Factory andZero ==
  some (.const () (.bitvecConst 32 0))
#guard (Core.EqualitySimplification.bvAndRule shadowedAnd andZero).isNone

/-! Absorption at every width the factory defines an `and` for. -/

private def andWidths : List Nat :=
  Core.Factory.toArray.toList.filterMap fun fn =>
    match Core.CoreOp.ofString fn.name.name with
    | .bv ⟨n, .And⟩ => some n
    | _ => none

#guard !andWidths.isEmpty && andWidths.all fun n =>
  let zero : Core.Expression.Expr := .const () (.bitvecConst n 0)
  let ones : Core.Expression.Expr :=
    .const () (.bitvecConst n (BitVec.allOnes n))
  Core.EqualitySimplification.bvAndRule Core.Factory (bvAndAt n varA zero)
      == some zero &&
    Core.EqualitySimplification.bvAndRule Core.Factory (bvAndAt n varA ones)
      == some varA

/-! A constant whose width differs from the op's is left alone. Surface syntax
rejects one as ill-typed, so the term is built here. -/

#guard (Core.EqualitySimplification.bvAndRule Core.Factory
  (bvAndAt 16 varA (.const () (.bitvecConst 8 255)))).isNone

/-! ### Agreement with the solver

Each program of this section, verified by `agreesWithSolver` in both modes. -/

/--
info: maskZero: pass
zeroFirst: pass
allOnes: pass
allOnesFirst: pass
nested: pass
exposed: pass
orZero: fail
xorAllOnes: fail
width1: pass
width8: pass
width16: pass
width64: pass
width128: pass
notAllOnes: fail


Obligation outsideAll: failed!

Result obtained during evaluation.


Obligation outsideAll: failed!

Result obtained during evaluation.
outsideAll: fail
inLemma: pass
inCondition: pass
underExists: pass
boundAllOnes: pass
inTrigger: fail
inCover: fail
viaDefinition: pass
afterDead: pass
maskZero: pass
zeroFirst: pass
allOnes: pass
allOnesFirst: pass
nested: pass
exposed: pass
orZero: fail
xorAllOnes: fail
width1: pass
width8: pass
width16: pass
width64: pass
width128: pass
notAllOnes: fail


Obligation outsideAll: failed!

Result obtained during evaluation.


Obligation outsideAll: failed!

Result obtained during evaluation.
outsideAll: fail
inLemma: pass
inCondition: pass
underExists: pass
boundAllOnes: pass
inTrigger: fail
inCover: fail
viaDefinition: pass
afterDead: pass
-/
#guard_msgs in
#eval agreeInBothModes [absorbPgm, anyAddressPgm, positionsBvPgm]

/-! ## `str.in_re` on a literal string

`str.in_re(s, r)` with a literal `s` and a regex `r` built from literals is
decided with SMT-LIB's meaning.

Each operator and its SMT-LIB edge cases, under a quantifier and a `fun`, in an
`if` and an `==`, in a `cover`, and in a lemma, and a selector goal with no
regex. Goals have no facts on their path; the `assume` folds to `false`, so
`afterDead` is left for the solver. -/

private def literalRePgm :=
#strata
program Core;
datatype Option () { None(), Some(val: int) };
lemma [inLemma]: str.in.re("ab", re.+(str.to.re("ab")));
procedure P(p : bool)
{
  assert [rate]: str.in.re("rate(30 days)",
    re.concat(str.to.re("rate("),
      re.concat(
        re.concat(
          re.union(re.range("1", "9"),
            re.concat(re.range("1", "9"), re.range("0", "9"))),
          re.union(str.to.re(" day"), str.to.re(" days"))),
        str.to.re(")"))));
  assert [noMatch]: !str.in.re("ab", re.loop(str.to.re("a"), 1, 3));
  assert [reversedRange]: !str.in.re("m", re.range("z", "a"));
  assert [multiCharRange]: !str.in.re("b", re.range("ab", "z"));
  assert [emptyRangeBound]: !str.in.re("a", re.range("", "z"));
  assert [loopReversed]: !str.in.re("aa", re.loop(str.to.re("a"), 2, 1));
  assert [loopReversedEmpty]: !str.in.re("", re.loop(str.to.re(""), 2, 1));
  assert [loopNullableBody]:
    str.in.re("", re.loop(re.*(str.to.re("a")), 2, 3));
  assert [loopZero]: str.in.re("", re.loop(str.to.re("a"), 0, 0));
  assert [compInter]: !str.in.re("x",
    re.inter(re.*(re.allchar()), re.comp(str.to.re("x"))));
  assert [allcharNonAscii]: str.in.re("é", re.allchar());
  assert [emptyString]: str.in.re("", re.*(str.to.re("a")));
  assert [plus]: str.in.re("abab", re.+(str.to.re("ab")));
  assert [reNone]: !str.in.re("", re.none());
  assert [reAll]: str.in.re("abc", re.all());
  assert [decidedFalse]: str.in.re("b", re.*(str.to.re("a")));
  assert [underQuant]:
    forall x : int :: str.in.re("a", re.all()) || int.gt(x, 0);
  assert [boundString]: forall x : string :: str.in.re(x, re.all());
  assert [inCondition]: if str.in.re("a", re.all()) then p else !p;
  assert [inEquality]: str.in.re("a", re.all()) == p;
  assert [inLambda]: (fun y : int => str.in.re("a", re.all())) ==
    (fun y : int => p);
  assert [selector]: Option..isSome(Some(1));
  cover [covered]: str.in.re("a", re.*(str.to.re("a")));
  cover [notCovered]: str.in.re("b", re.*(str.to.re("a")));
  assume str.in.re("b", re.*(str.to.re("a")));
  assert [afterDead]: str.in.re("a", re.*(str.to.re("a")));
};
#end

/--
info: program Core;

datatype Option {
  None(),
  Some(val : int)
};
lemma [inLemma]: true;
procedure P (p : bool)
{
  assert [rate]: true;
  assert [noMatch]: true;
  assert [reversedRange]: true;
  assert [multiCharRange]: true;
  assert [emptyRangeBound]: true;
  assert [loopReversed]: true;
  assert [loopReversedEmpty]: true;
  assert [loopNullableBody]: true;
  assert [loopZero]: true;
  assert [compInter]: true;
  assert [allcharNonAscii]: true;
  assert [emptyString]: true;
  assert [plus]: true;
  assert [reNone]: true;
  assert [reAll]: true;
  assert [decidedFalse]: false;
  assert [underQuant]: true;
  assert [boundString]: forall x : string :: str.in.re(x, re.all());
  assert [inCondition]: p;
  assert [inEquality]: true == p;
  assert [inLambda]: (fun y : int => true) == (fun y : int => p);
  assert [selector]: true;
  cover [covered]: true;
  cover [notCovered]: false;
  assume [assume_0]: str.in.re("b", re.*(str.to.re("a")));
  assert [afterDead]: str.in.re("a", re.*(str.to.re("a")));
};
-/
#guard_msgs in
#eval rewriteAndPrint literalRePgm

/-! A string made literal by an axiom or a definition is decided; a regex
variable, a non-literal string and a non-literal loop bound are not. A regex
returned by a 0-ary function is read only when the function is `inline`, since
only then is the call expanded. A definition's body is folded even when no
fact changes it. -/

private def factsRePgm :=
#strata
program Core;
const name : string;
axiom [rotation]: name == "rate(30 days)";
function bodilessRe () : regex;
function bodyRe () : regex { re.*(str.to.re("a")) }
inline function inlineRe () : regex { re.*(str.to.re("a")) }
procedure P(t : string, n : int)
{
  assert [bodiless]: str.in.re("a", bodilessRe());
  assert [withBody]: str.in.re("a", bodyRe());
  assert [inlineBody]: str.in.re("a", inlineRe());
  assert [fromAxiom]: str.in.re(name, re.concat(str.to.re("rate("),
    re.concat(re.+(re.range("0", "9")), str.to.re(" days)"))));
  var s : string := "rate(2 hours)";
  assert [fromDefinition]: !str.in.re(s, re.concat(str.to.re("rate("),
    re.concat(re.+(re.range("0", "9")), str.to.re(" days)"))));
  var r : regex := re.*(str.to.re("a"));
  assert [regexVariable]: str.in.re("a", r);
  assert [variable]: str.in.re(t, re.*(str.to.re("a")));
  assert [boundIsVariable]: str.in.re("a", re.loop(str.to.re("a"), n, 2));
  var b : bool := str.in.re("a", re.*(str.to.re("a")));
  assert [definedTest]: b;
  var y : int := int.add(1, 2);
  assert [definedSum]: y == 3;
};
#end

/--
info: program Core;

function name () : string;
axiom [rotation]: name == "rate(30 days)";
function bodilessRe () : regex;
function bodyRe () : regex {
  re.*(str.to.re("a"))
}
inline function inlineRe () : regex {
  re.*(str.to.re("a"))
}
procedure P (t : string, n : int)
{
  assert [bodiless]: str.in.re("a", bodilessRe);
  assert [withBody]: str.in.re("a", bodyRe);
  assert [inlineBody]: true;
  assert [fromAxiom]: true;
  var s : string := "rate(2 hours)";
  assert [fromDefinition]: true;
  var r : regex := re.*(str.to.re("a"));
  assert [regexVariable]: str.in.re("a", r);
  assert [variable]: str.in.re(t, re.*(str.to.re("a")));
  assert [boundIsVariable]: str.in.re("a", re.loop(str.to.re("a"), n, 2));
  var b : bool := str.in.re("a", re.*(str.to.re("a")));
  assert [definedTest]: true;
  var y : int := int.add(1, 2);
  assert [definedSum]: true;
};
-/
#guard_msgs in
#eval rewriteAndPrint factsRePgm

/-! The encoder rejects a loop with a variable bound, so `rejectedLoop` fails
without the phase; with it, the other disjunct folds to `true` and the goal
passes without a solver call. -/

private def encoderRejectedPgm :=
#strata
program Core;
procedure E(n : int)
{
  assert [rejectedLoop]: str.in.re("a", re.all()) ||
    str.in.re("a", re.loop(str.to.re("a"), n, 2));
};
#end

/--
info: rejectedLoop: pass
discharge calls: 0
rejectedLoop: fail
discharge calls: 0
-/
#guard_msgs in
#eval do
  countedDischarge encoderRejectedPgm
  countedDischarge encoderRejectedPgm (phase := false)

/-! `.*a.*` decided on strings of 5,000 characters, which the definitions
build from a 50-character literal: neither goal reaches the discharge. -/

private def longRePgm :=
#strata
program Core;
procedure L()
{
  var a50 : string := "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
  var b50 : string := "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
  var a500 : string := str.concat(a50, str.concat(a50, str.concat(a50,
    str.concat(a50, str.concat(a50, str.concat(a50, str.concat(a50,
    str.concat(a50, str.concat(a50, a50)))))))));
  var b500 : string := str.concat(b50, str.concat(b50, str.concat(b50,
    str.concat(b50, str.concat(b50, str.concat(b50, str.concat(b50,
    str.concat(b50, str.concat(b50, b50)))))))));
  var a5000 : string := str.concat(a500, str.concat(a500, str.concat(a500,
    str.concat(a500, str.concat(a500, str.concat(a500, str.concat(a500,
    str.concat(a500, str.concat(a500, a500)))))))));
  var b5000 : string := str.concat(b500, str.concat(b500, str.concat(b500,
    str.concat(b500, str.concat(b500, str.concat(b500, str.concat(b500,
    str.concat(b500, str.concat(b500, b500)))))))));
  assert [longMatch]: str.in.re(a5000,
    re.concat(re.all(), re.concat(str.to.re("a"), re.all())));
  assert [longNoMatch]: !str.in.re(b5000,
    re.concat(re.all(), re.concat(str.to.re("a"), re.all())));
};
#end

/--
info: longMatch: pass
longNoMatch: pass
discharge calls: 0
-/
#guard_msgs in
#eval countedDischarge longRePgm

/-! A code point above `0x2FFFF`, which no source literal can hold, leaves
`str.in_re` undecided. -/

private def outsideAlphabet : String := String.singleton (Char.ofNat 0x30000)

private def inRe (s : String) (r : Core.Expression.Expr) :
    Core.Expression.Expr :=
  .app () (.app () (.op () ⟨toString (Core.CoreOp.str .InRegEx), ()⟩ none)
    (.const () (.strConst s))) r

private def toRe (s : String) : Core.Expression.Expr :=
  .app () (.op () ⟨toString (Core.CoreOp.str .ToRegEx), ()⟩ none)
    (.const () (.strConst s))

private def reAll : Core.Expression.Expr :=
  .op () ⟨toString (Core.CoreOp.re .All), ()⟩ none

#guard (Core.EqualitySimplification.inRegexRule
  (inRe outsideAlphabet reAll)).isNone
#guard (Core.EqualitySimplification.inRegexRule
  (inRe "a" (toRe outsideAlphabet))).isNone
#guard Core.EqualitySimplification.inRegexRule (inRe "a" (toRe "a")) ==
  some (.const () (.boolConst true))

/-! A loop with a negative literal bound, or a range with a bound outside the
alphabet, is not read as a regex. -/

private def reLoop (a : Core.Expression.Expr) (lo hi : Int) :
    Core.Expression.Expr :=
  .app () (.app () (.app () (.op () ⟨toString (Core.CoreOp.re .Loop), ()⟩ none)
    a) (.const () (.intConst lo))) (.const () (.intConst hi))

private def reRange (lo hi : String) : Core.Expression.Expr :=
  .app () (.app () (.op () ⟨toString (Core.CoreOp.re .Range), ()⟩ none)
    (.const () (.strConst lo))) (.const () (.strConst hi))

#guard (Core.EqualitySimplification.regexOf? (reLoop (toRe "a") (-1) 2)).isNone
#guard (Core.EqualitySimplification.regexOf? (reLoop (toRe "a") 0 (-1))).isNone
#guard Core.EqualitySimplification.regexOf? (reLoop (toRe "a") 0 2) ==
  some (.loop (.str ['a']) 0 2)
#guard (Core.EqualitySimplification.regexOf?
  (reRange "a" outsideAlphabet)).isNone
#guard (Core.EqualitySimplification.regexOf?
  (reRange outsideAlphabet "a")).isNone
#guard Core.EqualitySimplification.regexOf? (reRange "a" "z") ==
  some (.range 'a' 'z')

/-! ### Agreement with the solver

Each program of this section except `encoderRejectedPgm`, verified by
`agreesWithSolver` in both modes. -/

/--
info:

Obligation decidedFalse: failed!

Result obtained during evaluation.


Obligation decidedFalse: failed!

Result obtained during evaluation.
inLemma: pass
rate: pass
noMatch: pass
reversedRange: pass
multiCharRange: pass
emptyRangeBound: pass
loopReversed: pass
loopReversedEmpty: pass
loopNullableBody: pass
loopZero: pass
compInter: pass
allcharNonAscii: pass
emptyString: pass
plus: pass
reNone: pass
reAll: pass
decidedFalse: fail
underQuant: pass
boundString: pass
inCondition: fail
inEquality: fail
inLambda: other
selector: pass
covered: other
notCovered: fail
afterDead: pass


Obligation bodiless: SMT Solver Crash! stderr:
solver stdout: (error "Regular expression variables are not supported.")




Obligation bodiless: SMT Solver Crash! stderr:
solver stdout: (error "Regular expression variables are not supported.")




Obligation bodiless: SMT Solver Crash! stderr:
solver stdout: (error "Regular expression variables are not supported.")


bodiless: other
withBody: pass
inlineBody: pass
fromAxiom: pass
fromDefinition: pass
regexVariable: pass
variable: fail
boundIsVariable: other
definedTest: pass
definedSum: pass
longMatch: pass
longNoMatch: pass


Obligation decidedFalse: failed!

Result obtained during evaluation.


Obligation decidedFalse: failed!

Result obtained during evaluation.
inLemma: pass
rate: pass
noMatch: pass
reversedRange: pass
multiCharRange: pass
emptyRangeBound: pass
loopReversed: pass
loopReversedEmpty: pass
loopNullableBody: pass
loopZero: pass
compInter: pass
allcharNonAscii: pass
emptyString: pass
plus: pass
reNone: pass
reAll: pass
decidedFalse: fail
underQuant: pass
boundString: pass
inCondition: fail
inEquality: fail
inLambda: other
selector: pass
covered: other
notCovered: fail
afterDead: pass


Obligation bodiless: SMT Solver Crash! stderr:
solver stdout: (error "Regular expression variables are not supported.")




Obligation bodiless: SMT Solver Crash! stderr:
solver stdout: (error "Regular expression variables are not supported.")




Obligation bodiless: SMT Solver Crash! stderr:
solver stdout: (error "Regular expression variables are not supported.")


bodiless: other
withBody: pass
inlineBody: pass
fromAxiom: pass
fromDefinition: pass
regexVariable: pass
variable: fail
boundIsVariable: other
definedTest: pass
definedSum: pass
longMatch: pass
longNoMatch: pass
-/
#guard_msgs in
#eval agreeInBothModes
  [literalRePgm, factsRePgm, longRePgm]

/-! ## Connectives with a literal argument

`and`, `or` and `==>` with a literal on either side are folded.

The tests cover each rule with the literal on either side, nested, through
`==`, under `forall` with and without a trigger, and in a definition.
`p ==> false` is kept, since its value `!p` is neither a literal nor an
operand. -/

private def connectivesPgm :=
#strata
program Core;
function f (n : int) : bool;
procedure Holds(p : bool, q : bool, r : bool, s : bool)
{
  var y : bool := p || q;
  assume [qHolds]: q;
  assert [orTrue]: p || q;
  assert [nested]: (p || q) || r;
  assert [impliesTrue]: p ==> q;
  assert [andTrue]: p && q;
  assert [andTrueLeft]: q && p;
  assert [impliesTrueLeft]: q ==> p;
  assert [impliesFalseLeft]: !q ==> p;
  assert [orFalseLeft]: !q || p;
  assert [impliesFalse]: p ==> !q;
  assert [repeated]: p || (if r || q then true else s);
  assert [throughEquality]: p || ((r || q) == true);
  assert [underForall]: forall n : int :: f(n) || q;
  assert [withTrigger]: forall n : int :: { f(n) } f(n) || q;
  assert [viaDefinition]: y;
};
procedure Fails(p : bool, q : bool, r : bool)
{
  assume [qFails]: !q;
  assert [andFalse]: p && q;
  assert [orFalse]: p || q;
  assert [unrelated]: p || r;
};
#end

/--
info: program Core;

function f (n : int) : bool;
procedure Holds (p : bool, q : bool, r : bool, s : bool)
{
  var y : bool := p || q;
  assume [qHolds]: q;
  assert [orTrue]: true;
  assert [nested]: true;
  assert [impliesTrue]: true;
  assert [andTrue]: p;
  assert [andTrueLeft]: p;
  assert [impliesTrueLeft]: p;
  assert [impliesFalseLeft]: true;
  assert [orFalseLeft]: p;
  assert [impliesFalse]: p ==> false;
  assert [repeated]: true;
  assert [throughEquality]: true;
  assert [underForall]: true;
  assert [withTrigger]: true;
  assert [viaDefinition]: true;
};
procedure Fails (p : bool, q : bool, r : bool)
{
  assume [qFails]: !q;
  assert [andFalse]: false;
  assert [orFalse]: p;
  assert [unrelated]: p || r;
};
-/
#guard_msgs in
#eval rewriteAndPrint connectivesPgm

-- With the phase, the goals that fold to `true` do not reach the discharge.
/--
info: orTrue: pass
nested: pass
impliesTrue: pass
andTrue: pass
andTrueLeft: pass
impliesTrueLeft: pass
impliesFalseLeft: pass
orFalseLeft: pass
impliesFalse: pass
repeated: pass
throughEquality: pass
underForall: pass
withTrigger: pass
viaDefinition: pass
andFalse: pass
orFalse: pass
unrelated: pass
discharge calls: 8
orTrue: pass
nested: pass
impliesTrue: pass
andTrue: pass
andTrueLeft: pass
impliesTrueLeft: pass
impliesFalseLeft: pass
orFalseLeft: pass
impliesFalse: pass
repeated: pass
throughEquality: pass
underForall: pass
withTrigger: pass
viaDefinition: pass
andFalse: pass
orFalse: pass
unrelated: pass
discharge calls: 17
-/
#guard_msgs in
#eval do
  countedDischarge connectivesPgm
  countedDischarge connectivesPgm (phase := false)

/-! A procedure with no facts, and an assumption that folds to `false`, which
leaves the goals after it alone. -/

private def connectivesDeadPgm :=
#strata
program Core;
procedure NoFacts(p : bool)
{
  assert [noFacts]: p || true;
};
procedure Dead(p : bool, q : bool)
{
  assume q;
  assume p && !q;
  assert [afterDead]: p || q;
};
#end

/--
info: program Core;

procedure NoFacts (p : bool)
{
  assert [noFacts]: true;
};
procedure Dead (p : bool, q : bool)
{
  assume [assume_0]: q;
  assume [assume_1]: p && !q;
  assert [afterDead]: p || q;
};
-/
#guard_msgs in
#eval rewriteAndPrint connectivesDeadPgm

/-! A lemma with no facts, a lemma that an axiom decides, and a `cover` that
an assumption makes unreachable. -/

private def connectivesPositionsPgm :=
#strata
program Core;
const p : bool;
const q : bool;
lemma [noFactsLemma]: p || true;
axiom [qAxiom]: q;
lemma [fromAxiom]: p || q;
procedure C(a : bool, b : bool)
{
  assume !b;
  cover [unreachable]: a && b;
};
#end

/--
info: program Core;

function p () : bool;
function q () : bool;
lemma [noFactsLemma]: true;
axiom [qAxiom]: q;
lemma [fromAxiom]: true;
procedure C (a : bool, b : bool)
{
  assume [assume_0]: !b;
  cover [unreachable]: false;
};
-/
#guard_msgs in
#eval rewriteAndPrint connectivesPositionsPgm

/-! A goal that needs more rounds of folding than `foldRounds` allows is left
partly folded, which keeps its value. -/

private def connectivesRoundsPgm :=
#strata
program Core;
procedure Rounds(p : bool, s : bool)
{
  assert [roundsRunOut]:
    p || (if p || (if p || (if p || (if p || (if p || (if p || (if p ||
      (if p || true then true else s) then true else s) then true else s)
      then true else s) then true else s) then true else s)
      then true else s) then true else s);
};
#end

/--
info: program Core;

procedure Rounds (p : bool, s : bool)
{
  assert [roundsRunOut]: p || (if true then true else s);
};
-/
#guard_msgs in
#eval rewriteAndPrint connectivesRoundsPgm

private def connectivesLimitPgm :=
#strata
program Core;
procedure L(x : int, p : bool)
{
  assume int.gt(x, 5);
  assume x == 1;
  assert [limit]: p && int.gt(x, 4);
};
#end

-- The phase's limitation: a goal on a contradictory path folds to `false`
-- and is reported failing without a solver call.
/--
info:

Obligation limit: failed!

Result obtained during evaluation.
limit: fail
discharge calls: 0
limit: pass
discharge calls: 1
-/
#guard_msgs in
#eval do
  let options := { Core.VerifyOptions.quiet with
    checkMode := .deductiveAssumingSatisfiablePaths }
  countedDischarge connectivesLimitPgm (options := options)
  countedDischarge connectivesLimitPgm (phase := false) (options := options)

private def connectivesGuardPgm :=
#strata
program Core;
procedure G(x : int, p : bool, q : bool)
{
  if (int.gt(x, 5) && int.lt(x, 3)) {
    assume !q;
    assert [guardLimit]: p && q;
  }
};
#end

-- The phase does not use an `if` guard as a fact, so a goal under a
-- contradictory guard also folds to `false`.
/--
info:

Obligation guardLimit: failed!

Result obtained during evaluation.
guardLimit: fail
discharge calls: 0
guardLimit: pass
discharge calls: 1
-/
#guard_msgs in
#eval do
  let options := { Core.VerifyOptions.quiet with
    checkMode := .deductiveAssumingSatisfiablePaths }
  countedDischarge connectivesGuardPgm (options := options)
  countedDischarge connectivesGuardPgm (phase := false) (options := options)

/-! ### Agreement with the solver

Each program of this section except `connectivesLimitPgm` and
`connectivesGuardPgm`, verified by `agreesWithSolver` in both modes. Those two
fold a goal on a contradictory path to `false`, so the end of the file checks
them in deductive mode only. -/

/--
info: orTrue: pass
nested: pass
impliesTrue: pass
andTrue: fail
andTrueLeft: fail
impliesTrueLeft: fail
impliesFalseLeft: pass
orFalseLeft: fail
impliesFalse: fail
repeated: pass
throughEquality: pass
underForall: pass
withTrigger: pass
viaDefinition: pass
andFalse: fail
orFalse: fail
unrelated: fail
noFacts: pass
afterDead: pass
noFactsLemma: pass
fromAxiom: pass
unreachable: fail
roundsRunOut: pass


Obligation andFalse: failed!

Result obtained during evaluation.


Obligation andFalse: failed!

Result obtained during evaluation.
orTrue: pass
nested: pass
impliesTrue: pass
andTrue: fail
andTrueLeft: fail
impliesTrueLeft: fail
impliesFalseLeft: pass
orFalseLeft: fail
impliesFalse: fail
repeated: pass
throughEquality: pass
underForall: pass
withTrigger: pass
viaDefinition: pass
andFalse: fail
orFalse: fail
unrelated: fail
noFacts: pass
afterDead: pass
noFactsLemma: pass
fromAxiom: pass
unreachable: fail
roundsRunOut: pass
-/
#guard_msgs in
#eval agreeInBothModes [connectivesPgm, connectivesDeadPgm,
  connectivesPositionsPgm, connectivesRoundsPgm]

/-! ## Folding without facts

A goal is folded even when no fact is on its path, an assumption that folds to
`false` marks its path dead, and a definition's body is folded before it is
substituted, even when no fact changes it. -/

private def noFactsPgm :=
#strata
program Core;
datatype Option () { None(), Some(val: int) };
procedure NoFacts()
{
  assert [noFacts]: Option..isSome(Some(1));
};
procedure Dead(x : int)
{
  assume int.lt(1, 0);
  assert [afterDead]: Option..isSome(Some(x));
};
procedure FoldedDef()
{
  var y : bool := Option..isSome(Some(1));
  assert [foldedDef]: y;
};
#end

/--
info: program Core;

datatype Option {
  None(),
  Some(val : int)
};
procedure NoFacts ()
{
  assert [noFacts]: true;
};
procedure Dead (x : int)
{
  assume [assume_0]: int.lt(1, 0);
  assert [afterDead]: Option..isSome(Some(x));
};
procedure FoldedDef ()
{
  var y : bool := Option..isSome(Some(1));
  assert [foldedDef]: true;
};
-/
#guard_msgs in
#eval rewriteAndPrint noFactsPgm

/-! ## Existentials witnessed by a fact

An existential `exists x :: { f(x) } P(x)` becomes `true` when `P(v)` folds to
`true` for a fact `f(v)`. Most tests type check first, since a call of a
polymorphic function carries its instantiated type only after type checking.

The hint proves `outside`; the other existentials are left alone, never
decided `false`. -/

private def hintPgm :=
#strata
program Core;
function hint (a : bv W32) : bool;
axiom [hintZero]: hint(bv{32}(0));
lemma [outside]: exists a : bv W32 :: { hint(a) }
  !(bv32.and(a, bv{32}(4294967040)) == bv{32}(167772416));
lemma [noSolution]: exists a : bv W32 :: { hint(a) }
  bv32.and(a, bv{32}(4294967040)) == bv{32}(1);
lemma [inside]: exists a : bv W32 :: { hint(a) }
  bv32.and(a, bv{32}(4294967040)) == bv{32}(167772416);
lemma [noTrigger]: exists a : bv W32 :: bv32.and(a, bv{32}(1)) == a;
#end

/--
info: program Core;

function hint (a : bv W32) : bool;
axiom [hintZero]: hint(bv{32}(0));
lemma [outside]: true;
lemma [noSolution]: exists a : (bv W32) ::  { hint(a) }
  bv32.and(a, bv{32}(4294967040)) == bv{32}(1);
lemma [inside]: exists a : (bv W32) ::  { hint(a) }
  bv32.and(a, bv{32}(4294967040)) == bv{32}(167772416);
lemma [noTrigger]: exists a : (bv W32) :: bv32.and(a, bv{32}(1)) == a;
-/
#guard_msgs in
#eval rewriteAndPrint hintPgm (typeCheck := true)

/-! Witnessed existentials in other positions, with two candidates, and with
the hint in any term or group of the trigger. One before its hint is left
alone; a closed one under a binder is witnessed, since folding reaches
quantifier bodies. In `twoVariables` the trigger is on the inner variable, so
the inner quantifier is witnessed, and the outer one, whose variable is then
unused, is dropped. -/

private def positionsPgm :=
#strata
program Core;
function hint (a : int) : bool;
function other (a : int) : bool;
function g () : bool;
lemma [beforeHint]: exists a : int :: { hint(a) } a == 1;
axiom [hintOne]: hint(1);
axiom [hintTwo]: hint(2);
lemma [negated]: !(exists a : int :: { hint(a) } a == 1);
lemma [inEquality]: (exists a : int :: { hint(a) } a == 1) == g();
lemma [inCondition]:
  if (exists a : int :: { hint(a) } a == 1) then g() else !g();
lemma [inThen]:
  if g() then (exists a : int :: { hint(a) } a == 1) else g();
lemma [implies]: (exists a : int :: { hint(a) } a == 1) ==> g();
lemma [witnessOne]: exists a : int :: { hint(a) } a == 1;
lemma [witnessTwo]: exists a : int :: { hint(a) } a == 2;
lemma [underForall]: forall b : int :: exists a : int :: { hint(a) } a == 1;
lemma [twoVariables]: exists a : int, b : int :: { hint(b) } b == 1;
lemma [firstTerm]: exists a : int :: { hint(a), other(a) } a == 1;
lemma [secondTerm]: exists a : int :: { other(a), hint(a) } a == 1;
lemma [firstGroup]: exists a : int :: { hint(a) } { other(a) } a == 1;
lemma [secondGroup]: exists a : int :: { other(a) } { hint(a) } a == 1;
#end

/--
info: program Core;

function hint (a : int) : bool;
function other (a : int) : bool;
function g () : bool;
lemma [beforeHint]: exists a : int ::  { hint(a) }
  a == 1;
axiom [hintOne]: hint(1);
axiom [hintTwo]: hint(2);
lemma [negated]: false;
lemma [inEquality]: true == g;
lemma [inCondition]: g;
lemma [inThen]: if g then true else g;
lemma [implies]: g;
lemma [witnessOne]: true;
lemma [witnessTwo]: true;
lemma [underForall]: true;
lemma [twoVariables]: true;
lemma [firstTerm]: true;
lemma [secondTerm]: true;
lemma [firstGroup]: true;
lemma [secondGroup]: true;
-/
#guard_msgs in
#eval rewriteAndPrint positionsPgm (typeCheck := true)

/-! Existentials the fact `hint(1)` does not witness, though both hold. A
trigger on the outer variable of a two-variable existential sits on the inner
quantifier, where it is not applied to that quantifier's own variable, so
`outerTrigger` is left alone. A candidate's body is folded without the facts,
so in `ownTrigger` the body `hint(1)` stays and the existential is left
alone. -/

private def hintScopePgm :=
#strata
program Core;
function hint (a : int) : bool;
axiom [hintOne]: hint(1);
lemma [outerTrigger]: exists a : int, b : int :: { hint(a) }
  a == b && a == 1;
lemma [ownTrigger]: exists a : int :: { hint(a) } hint(a);
#end

/--
info: program Core;

function hint (a : int) : bool;
axiom [hintOne]: hint(1);
lemma [outerTrigger]: exists a : int :: exists b : int ::  { hint(a) }
  a == b && a == 1;
lemma [ownTrigger]: exists a : int ::  { hint(a) }
  hint(a);
-/
#guard_msgs in
#eval rewriteAndPrint hintScopePgm (typeCheck := true)

/-! The fact `hint(0)` of a polymorphic `hint` is about an `int`, so it does
not witness the false `bool` existential `wrongType`, and witnesses the `int`
existential `rightType`. The fact `hint(bv{8}(0))` does not witness the 32-bit
existential `wrongWidth`. -/

private def polyHintPgm :=
#strata
program Core;
function hint<T> (a : T) : bool;
axiom [hintZero]: hint(0);
axiom [hintByte]: hint(bv{8}(0));
lemma [wrongType]: exists b : bool :: { hint(b) }
  !(b == true) && !(b == false);
lemma [rightType]: exists b : int :: { hint(b) } b == 0;
lemma [wrongWidth]: exists a : bv W32 :: { hint(a) } a == bv{32}(0);
#end

/--
info: program Core;

function hint<T> (a : T) : bool;
axiom [hintZero]: hint(0);
axiom [hintByte]: hint(bv{8}(0));
lemma [wrongType]: exists b : bool ::  { hint(b) }
  !(b == true) && !(b == false);
lemma [rightType]: true;
lemma [wrongWidth]: exists a : (bv W32) ::  { hint(a) }
  a == bv{32}(0);
-/
#guard_msgs in
#eval rewriteAndPrint polyHintPgm (typeCheck := true)

/-! Without type checking, a call of the polymorphic `hint` carries its generic
type `T → bool`, so `rightType` is left alone. -/

/--
info: program Core;

function hint<T> (a : T) : bool;
axiom [hintZero]: hint(0);
axiom [hintByte]: hint(bv{8}(0));
lemma [wrongType]: exists b : bool ::  { hint(b) }
  !(b == true) && !(b == false);
lemma [rightType]: exists b : int ::  { hint(b) }
  b == 0;
lemma [wrongWidth]: exists a : (bv W32) ::  { hint(a) }
  a == bv{32}(0);
-/
#guard_msgs in
#eval rewriteAndPrint polyHintPgm

/-! Hints in a procedure: a hint that is not a value, a hint forgotten after
its branch, and a contradictory path. -/

private def hintProcPgm :=
#strata
program Core;
function hint (a : int) : bool;
procedure P(x : int)
{
  assume hint(x);
  assert [nonValue]: exists a : int :: { hint(a) } a == x;
  assume hint(3);
  assert [assumed]: exists a : int :: { hint(a) } int.gt(a, 2);
  cover [covered]: exists a : int :: { hint(a) } a == 3;
  if (x == 0) {
    assume hint(4);
    assert [inBranch]: exists a : int :: { hint(a) } a == 4;
  }
  assert [afterBranch]: exists a : int :: { hint(a) } a == 4;
  assume int.lt(1, 0);
  assert [dead]: exists a : int :: { hint(a) } a == 3;
};
#end

/--
info: program Core;

function hint (a : int) : bool;
procedure P (x : int)
{
  assume [assume_0]: hint(x);
  assert [nonValue]: exists a : int ::  { hint(a) }
    a == x;
  assume [assume_1]: hint(3);
  assert [assumed]: true;
  cover [covered]: true;
  if (x == 0) {
    assume [assume_2]: hint(4);
    assert [inBranch]: true;
  }
  assert [afterBranch]: exists a : int ::  { hint(a) }
    a == 4;
  assume [assume_3]: int.lt(1, 0);
  assert [dead]: exists a : int ::  { hint(a) }
    a == 3;
};
-/
#guard_msgs in
#eval rewriteAndPrint hintProcPgm (typeCheck := true)

-- Through the pipeline, the goals left alone above and the cover reach the
-- discharge. It answers every query unsat, so the cover fails.
/--
info: nonValue: pass
assumed: pass
covered: fail
inBranch: pass
afterBranch: pass
dead: pass
discharge calls: 4
-/
#guard_msgs in
#eval countedDischarge hintProcPgm

private def undetectedPgm :=
#strata
program Core;
function hint (a : int) : bool;
procedure Undetected(x : int)
{
  assume hint(0);
  assume int.gt(x, 5);
  assume x == 1;
  assert [undetected]: !(exists a : int :: { hint(a) } a == 0);
};
#end

-- The phase misses this contradiction, so the goal folds to `false` and fails.
/--
info:

Obligation undetected: failed!

Result obtained during evaluation.
undetected: fail
discharge calls: 0
-/
#guard_msgs in
#eval countedDischarge undetectedPgm
  (options := { Core.VerifyOptions.quiet with
    checkMode := .deductiveAssumingSatisfiablePaths })

/-! An existential in a definition body or an assumption is witnessed too: `y`
reads as `true`, and the assumption folds to `false` and marks its path dead.
A write to `z` keeps the hints. -/

private def hintFlowPgm :=
#strata
program Core;
function hint (a : int) : bool;
procedure Flow()
{
  var z : int;
  assume hint(3);
  var y : bool := exists a : int :: { hint(a) } a == 3;
  z := 1;
  assert [afterWrite]: exists a : int :: { hint(a) } a == 3;
  assert [fromDef]: y;
};
procedure DeadByExists()
{
  assume hint(1);
  assume !(exists a : int :: { hint(a) } a == 1);
  assert [deadByExists]: exists a : int :: { hint(a) } a == 1;
};
#end

/--
info: program Core;

function hint (a : int) : bool;
procedure Flow ()
{
  var z : int;
  assume [assume_0]: hint(3);
  var y : bool := exists a : int ::  { hint(a) }
    a == 3;
  z := 1;
  assert [afterWrite]: true;
  assert [fromDef]: true;
};
procedure DeadByExists ()
{
  assume [assume_1]: hint(1);
  assume [assume_2]: !(exists a : int ::  { hint(a) }
    a == 1);
  assert [deadByExists]: exists a : int ::  { hint(a) }
    a == 1;
};
-/
#guard_msgs in
#eval rewriteAndPrint hintFlowPgm (typeCheck := true)

/-! Only the 16 most recent candidates are tried: `hint(2)` witnesses
`lastTried`, and `hint(1)`, the seventeenth, does not witness `notTried`. -/

private def hintLimitPgm :=
#strata
program Core;
function hint (a : int) : bool;
axiom [h1]: hint(1);
axiom [h2]: hint(2);
axiom [h3]: hint(3);
axiom [h4]: hint(4);
axiom [h5]: hint(5);
axiom [h6]: hint(6);
axiom [h7]: hint(7);
axiom [h8]: hint(8);
axiom [h9]: hint(9);
axiom [h10]: hint(10);
axiom [h11]: hint(11);
axiom [h12]: hint(12);
axiom [h13]: hint(13);
axiom [h14]: hint(14);
axiom [h15]: hint(15);
axiom [h16]: hint(16);
axiom [h17]: hint(17);
lemma [notTried]: exists a : int :: { hint(a) } a == 1;
lemma [lastTried]: exists a : int :: { hint(a) } a == 2;
#end

/--
info: program Core;

function hint (a : int) : bool;
axiom [h1]: hint(1);
axiom [h2]: hint(2);
axiom [h3]: hint(3);
axiom [h4]: hint(4);
axiom [h5]: hint(5);
axiom [h6]: hint(6);
axiom [h7]: hint(7);
axiom [h8]: hint(8);
axiom [h9]: hint(9);
axiom [h10]: hint(10);
axiom [h11]: hint(11);
axiom [h12]: hint(12);
axiom [h13]: hint(13);
axiom [h14]: hint(14);
axiom [h15]: hint(15);
axiom [h16]: hint(16);
axiom [h17]: hint(17);
lemma [notTried]: exists a : int ::  { hint(a) }
  a == 1;
lemma [lastTried]: true;
-/
#guard_msgs in
#eval rewriteAndPrint hintLimitPgm (typeCheck := true)

/-! ### Agreement with the solver

Each program of this section and the one before it except `undetectedPgm`,
verified by `agreesWithSolver` in both modes. `undetectedPgm` folds a goal on
a contradictory path to `false`, so the end of the file checks it in deductive
mode only. -/

/--
info: noFacts: pass
afterDead: pass
foldedDef: pass
outside: pass
noSolution: other
inside: other
noTrigger: pass
beforeHint: pass
negated: fail
inEquality: fail
inCondition: fail
inThen: fail
implies: fail
witnessOne: pass
witnessTwo: pass
underForall: pass
twoVariables: pass
firstTerm: pass
secondTerm: pass
firstGroup: pass
secondGroup: pass
outerTrigger: pass
ownTrigger: pass
wrongType: fail
rightType: pass
wrongWidth: pass
nonValue: pass
assumed: pass
covered: other
inBranch: pass
afterBranch: pass
dead: pass
afterWrite: pass
fromDef: pass
deadByExists: pass
notTried: pass
lastTried: pass
noFacts: pass
afterDead: pass
foldedDef: pass
outside: pass
noSolution: other
inside: other
noTrigger: pass


Obligation negated: failed!

Result obtained during evaluation.


Obligation negated: failed!

Result obtained during evaluation.
beforeHint: pass
negated: fail
inEquality: fail
inCondition: fail
inThen: fail
implies: fail
witnessOne: pass
witnessTwo: pass
underForall: pass
twoVariables: pass
firstTerm: pass
secondTerm: pass
firstGroup: pass
secondGroup: pass
outerTrigger: pass
ownTrigger: pass
wrongType: fail
rightType: pass
wrongWidth: pass
nonValue: pass
assumed: pass
covered: other
inBranch: pass
afterBranch: pass
dead: pass
afterWrite: pass
fromDef: pass
deadByExists: pass
notTried: pass
lastTried: pass
-/
#guard_msgs in
#eval agreeInBothModes
  [noFactsPgm, hintPgm, positionsPgm, hintScopePgm, polyHintPgm, hintProcPgm,
    hintFlowPgm, hintLimitPgm]

/-! ## Contradictory paths in deductive mode

The programs whose goal on a contradictory path folds to `false`, verified by
`agreesWithSolver` in deductive mode, where the solver proves such a goal.
`deductiveAssumingSatisfiablePaths` is left out: there the phase's run reports
the folded goal failing without a solver, as the tests above show. -/

/--
info: unseenContradiction: pass
undetected: pass
undetectedQuant: pass
limit: pass
guardLimit: pass
undetected: pass
-/
#guard_msgs in
#eval do
  let ps : List StrataDDM.Program := [unseenContradictionPgm, undetectedBvPgm,
    undetectedQuantPgm, connectivesLimitPgm, connectivesGuardPgm, undetectedPgm]
  for p in ps do
    agreesWithSolver .deductive p

/-! ## The fixtures' goals are typed, before the phase and after it

The theorems of `Strata.Transform.EqualitySimplificationCorrect` take as premise that the
goals of a body have values in the stores it reaches (`GoalsDefined`), and a goal has one
there when it is well typed. This check counts the goals, lemmas and axioms of the fixtures
that type check (all but `shadowDefPgm`, which the type checker rejects by design) and those
that `LExpr.typeCheck` types at `bool`, as type checking leaves them and after the phase. It
is evidence that the premises can hold, not that the folding conditions do. -/

private partial def stmtGoals : Core.Statement → List Core.Expression.Expr
  | .cmd (.cmd (.assert _ e _)) | .cmd (.cmd (.cover _ e _)) => [e]
  | .block _ ss _ | .loop _ _ _ ss _ => ss.flatMap stmtGoals
  | .ite _ ts es _ => ts.flatMap stmtGoals ++ es.flatMap stmtGoals
  | _ => []

/-- The goals, lemmas and axioms of a program. -/
private def programGoals (p : Core.Program) : List Core.Expression.Expr :=
  p.decls.flatMap fun
    | .proc q _ => match q.body with
      | .structured ss => ss.flatMap stmtGoals
      | _ => []
    | .ax a _ => [a.e]
    | .lemma l _ => [l.e]
    | _ => []

/-- How many of the goals, lemmas and axioms of `p` there are, and how many type at `bool`. -/
private def typedCount (p : Core.Program) : Nat × Nat :=
  let gs := programGoals p
  (gs.length, (gs.filter fun e => Lambda.LExpr.typeCheck [] e == some .bool).length)

/-- For the fixture `p`, `typedCount` as type checking leaves it and after the phase. -/
private def typedBeforeAfter (p : StrataDDM.Program) :
    Except String ((Nat × Nat) × (Nat × Nat)) := do
  let prog ← (Core.typeCheck .quiet (parse p)).mapError (fun e => toString e.message)
  let (_, out) ← (Core.Transform.run prog Core.EqualitySimplification.runEqualitySimplification
    { Core.Transform.CoreTransformState.emp with factory := Core.Factory }).mapError toString
  return (typedCount prog, typedCount out)

/-- The fixtures that type check. -/
private def fixtures : List (String × StrataDDM.Program) :=
  [("literalPgm", literalPgm),
   ("constructorPgm", constructorPgm),
   ("applicationPgm", applicationPgm),
   ("booleanPgm", booleanPgm),
   ("coverPgm", coverPgm),
   ("residualPgm", residualPgm),
   ("unusedPgm", unusedPgm),
   ("foldFirstPgm", foldFirstPgm),
   ("foldAxiomsPgm", foldAxiomsPgm),
   ("axiomPgm", axiomPgm),
   ("conjunctionPgm", conjunctionPgm),
   ("definitionPgm", definitionPgm),
   ("opaqueEqPgm", opaqueEqPgm),
   ("depthPgm", depthPgm),
   ("shadowPgm", shadowPgm),
   ("axiomAfterPgm", axiomAfterPgm),
   ("contradictionPgm", contradictionPgm),
   ("lemmaPgm", lemmaPgm),
   ("lemmaOrderPgm", lemmaOrderPgm),
   ("lemmaContradictionPgm", lemmaContradictionPgm),
   ("lemmaQuantPgm", lemmaQuantPgm)]

/--
info: before: 49 of 49 typed at bool; after: 49 of 49
-/
#guard_msgs in
#eval show IO Unit from do
  let ps := fixtures
  let mut before : Nat × Nat := (0, 0)
  let mut after : Nat × Nat := (0, 0)
  for (name, p) in ps do
    match typedBeforeAfter p with
    | .ok (b, a) =>
      before := (before.1 + b.1, before.2 + b.2)
      after := (after.1 + a.1, after.2 + a.2)
    | .error msg => IO.println s!"{name}: {msg}"
  IO.println s!"before: {before.2} of {before.1} typed at bool; after: {after.2} of {after.1}"

/-! ## The fixtures' operators are consistent with the folding factories

The theorems of `Strata.Transform.EqualitySimplificationCorrect` take as premise that the
operators of a body's commands (`CmdOps`) and of the ground axioms (`GroundAxiomsOps`) are
annotated at instances of their signatures in the folding factory the phase uses. This
check decides it, with `opsConsistentB`, which is sound for `Lambda.OpsConsistentR`
(`opsConsistentR_of_opsConsistentB`), on every fixture that type checks: against the
folding factory of `runCtx program F0` for the program as type checking leaves it, and of
`runCtx mid F0'` for the program `mid` that axiom folding gives, then on the output of the
phase. It counts the expressions checked (the goals, assumptions and definition values of
the bodies, and the ground axioms), those that pass, the operator nodes, and those the
folding factory knows. -/

private partial def stmtCmdExprs : Core.Statement → List Core.Expression.Expr
  | .cmd (.cmd (.assert _ e _)) | .cmd (.cmd (.cover _ e _)) | .cmd (.cmd (.assume _ e _))
  | .cmd (.cmd (.init _ _ (.det e) _)) => [e]
  | .block _ ss _ | .loop _ _ _ ss _ => ss.flatMap stmtCmdExprs
  | .ite _ ts es _ => ts.flatMap stmtCmdExprs ++ es.flatMap stmtCmdExprs
  | _ => []

/-- The expressions of the bodies' commands and the ground axioms of `p`. -/
private def premiseExprs (p : Core.Program) : List Core.Expression.Expr :=
  p.decls.flatMap fun
    | .proc q _ => match q.body with
      | .structured ss => ss.flatMap stmtCmdExprs
      | _ => []
    | .ax a _ => if a.e.hasBVar then [] else [a.e]
    | _ => []

private partial def opNames : Core.Expression.Expr → List String
  | .op _ n _ => [n.name]
  | .app _ f a | .eq _ f a => opNames f ++ opNames a
  | .abs _ _ _ b => opNames b
  | .ite _ c t f => opNames c ++ opNames t ++ opNames f
  | .quant _ _ _ _ tr b => opNames tr ++ opNames b
  | _ => []

/-- For `p` and its folding factory: expressions, passing ones, operators, known ones. -/
private def opsCount (p : Core.Program) : Except String (Nat × Nat × Nat × Nat) := do
  let F0 ← (Core.Transform.run p Core.Simplify.programFactory
    { Core.Transform.CoreTransformState.emp with factory := Core.Factory }).mapError toString
  let F := (Core.FoldAxioms.runCtx p F0).foldFactory
  let es := premiseExprs p
  let ops := es.flatMap opNames
  return (es.length,
    (es.filter (Core.EqualitySimplification.GoalsDefinedTest.opsConsistentB F)).length,
    ops.length, (ops.filter fun n => F[n]?.isSome).length)

private def addCounts (a b : Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2 + b.2.2.2)

private def showCounts (label : String) (c : Nat × Nat × Nat × Nat) : String :=
  s!"{label}: {c.2.1} of {c.1} consistent, {c.2.2.2} of {c.2.2.1} operators known"

/--
info: program: 87 of 87 consistent, 116 of 116 operators known
after axiom folding: 87 of 87 consistent, 114 of 114 operators known
after the phase: 87 of 87 consistent, 80 of 80 operators known
-/
#guard_msgs in
#eval show IO Unit from do
  let mut c₁ : Nat × Nat × Nat × Nat := (0, 0, 0, 0)
  let mut c₂ : Nat × Nat × Nat × Nat := (0, 0, 0, 0)
  let mut c₃ : Nat × Nat × Nat × Nat := (0, 0, 0, 0)
  for (name, p) in fixtures do
    let r : Except String _ := do
      let prog ← (Core.typeCheck .quiet (parse p)).mapError (fun e => toString e.message)
      let st := { Core.Transform.CoreTransformState.emp with factory := Core.Factory }
      let (_, mid) ← (Core.Transform.run prog Core.FoldAxioms.runFoldAxioms st).mapError toString
      let (_, out) ← (Core.Transform.run mid
        Core.EqualitySimplification.runEqualitySimplification st).mapError toString
      return (← opsCount prog, ← opsCount mid, ← opsCount out)
    match r with
    | .ok (a, b, c) => c₁ := addCounts c₁ a; c₂ := addCounts c₂ b; c₃ := addCounts c₃ c
    | .error msg => IO.println s!"{name}: {msg}"
  IO.println (showCounts "program" c₁)
  IO.println (showCounts "after axiom folding" c₂)
  IO.println (showCounts "after the phase" c₃)

/-! ## Near misses of the operator premise

`Core.EqualitySimplification.GoalsDefinedTest.wrongArg` and `wrongBeta` satisfy the operator
premise and have no value in any runtime factory (`wrongArg_no_value`, `wrongBeta_no_value`),
so the one-way folding conditions say nothing about them, though `wrongBeta` folds to the
integer `3`. `mistypedSum` fails the premise. -/

open Core.EqualitySimplification.GoalsDefinedTest in
#guard opsConsistentB Core.Factory wrongArg && opsConsistentB Core.Factory wrongBeta &&
  Core.Simplify.fold Core.Factory 100 wrongBeta == .intConst () 3 &&
  !opsConsistentB Core.Factory Core.FoldAxioms.mistypedSum

/-! Equality simplification folds goals with `foldTerm`, which `FoldSound` is about: it
also folds the counterexample and the beta near miss to the integer `3`. -/

open Core.EqualitySimplification.GoalsDefinedTest in
#guard Core.EqualitySimplification.foldTerm Core.Factory {} 100 Core.FoldAxioms.mistypedSum ==
    .intConst () 3 &&
  Core.EqualitySimplification.foldTerm Core.Factory {} 100 wrongBeta == .intConst () 3 &&
  Core.EqualitySimplification.foldTerm Core.Factory {} 100 wrongArg == wrongArg

/-! ## Witness candidates must have the quantifier's type

`foldTerm` proves `exists x : ty :: { f(x) } P(x)` when `P(v)` folds to `true` for a witness
candidate `v` the facts record for `f`. A candidate of another type can satisfy a body that no
value of `ty` does: `∃ x : bool. ¬(x == true) ∧ ¬(x == false)` is well typed and false, and
folds to `true` given the integer candidate `3`, since `3 == true` and `3 == false` fold to
`false`. So the facts the equality simplification theorems carry record candidates of the
quantifier's type (`Facts.Ops`); with the candidate `true`, the existential is not folded. -/

open Core.EqualitySimplification.GoalsDefinedTest in
private def tgTy : Lambda.LMonoTy := .tcons "TriggerGroup" []

open Core.EqualitySimplification.GoalsDefinedTest in
/-- `∃ x : bool :: { f(x) } ¬(x == true) ∧ ¬(x == false)`, with `f : bool → bool`. -/
private def noBool : Core.Expression.Expr :=
  let x : Core.Expression.Expr := .bvar () 0
  let notE (a : Core.Expression.Expr) : Core.Expression.Expr :=
    .app () (.op () ⟨"Bool.Not", ()⟩ (some (arr boolTy boolTy))) a
  let trig : Core.Expression.Expr :=
    .app () (.app () (.op () ⟨"TriggerGroup.addTrigger", ()⟩ (some (arr boolTy (arr tgTy tgTy))))
      (.app () (.op () ⟨"f", ()⟩ (some (arr boolTy boolTy))) x))
      (.op () ⟨"TriggerGroup.empty", ()⟩ (some tgTy))
  .quant () .exist "x" (some boolTy) trig
    (.app () (.app () (.op () ⟨"Bool.And", ()⟩ (some (arr boolTy (arr boolTy boolTy))))
      (notE (.eq () x (.boolConst () true)))) (notE (.eq () x (.boolConst () false))))

open Core.EqualitySimplification.GoalsDefinedTest in
/-- Facts recording the witness candidate `v` for `f : bool → bool`. -/
private def candidate (v : Core.Expression.Expr) : Core.EqualitySimplification.Facts :=
  { hints := ({} : Std.HashMap _ _).insert ("f", arr boolTy boolTy) [v] }

#guard Lambda.LExpr.typeCheck [] noBool == some .bool
#guard Core.EqualitySimplification.foldTerm Core.Factory (candidate (.intConst () 3)) 100 noBool ==
  .boolConst () true
#guard Core.EqualitySimplification.foldTerm Core.Factory (candidate (.boolConst () true)) 100
  noBool == Core.EqualitySimplification.foldTerm Core.Factory {} 100 noBool
#guard !(Core.EqualitySimplification.foldTerm Core.Factory {} 100 noBool).isTrue

/-! The same search over `int`, `∃ x : int :: { g(x) } x == 3 ∧ x == 4` given the Boolean
candidate `true`, does not fire: `true == 3` and `true == 4` fold to `false`, so the body
folds to `false` too. -/

open Core.EqualitySimplification.GoalsDefinedTest in
/-- `∃ x : int :: { g(x) } x == 3 ∧ x == 4`, with `g : int → bool`. -/
private def threeAndFour : Core.Expression.Expr :=
  let x : Core.Expression.Expr := .bvar () 0
  let trig : Core.Expression.Expr :=
    .app () (.app () (.op () ⟨"TriggerGroup.addTrigger", ()⟩ (some (arr boolTy (arr tgTy tgTy))))
      (.app () (.op () ⟨"g", ()⟩ (some (arr intTy boolTy))) x))
      (.op () ⟨"TriggerGroup.empty", ()⟩ (some tgTy))
  .quant () .exist "x" (some intTy) trig
    (.app () (.app () (.op () ⟨"Bool.And", ()⟩ (some (arr boolTy (arr boolTy boolTy))))
      (.eq () x (.intConst () 3))) (.eq () x (.intConst () 4)))

open Core.EqualitySimplification.GoalsDefinedTest in
private def trueCandidate : Core.EqualitySimplification.Facts :=
  { hints := ({} : Std.HashMap _ _).insert ("g", arr intTy boolTy) [.boolConst () true] }
open Core.EqualitySimplification.GoalsDefinedTest in
#guard Lambda.LExpr.typeCheck [] threeAndFour == some .bool &&
  !(Core.EqualitySimplification.foldTerm Core.Factory
    trueCandidate 100 threeAndFour).isTrue

/-! ## Recorded witness candidates are typed

The facts the theorems carry record each witness candidate for `f : ty → bool` at type `ty`
(`Facts.Ops`). Candidates come from assumptions and ground axioms `f(v)`, where `v` is often
a term over the program's variables. A variable keeps the type annotation type checking
gives it, so `LExpr.typeCheck []` types such a candidate. This check learns every assumption
and ground axiom of each program of this file that type checks, from no facts, and counts the
candidates recorded and those of their key's type. -/

private partial def stmtAssumes : Core.Statement → List Core.Expression.Expr
  | .cmd (.cmd (.assume _ e _)) => [e]
  | .block _ ss _ | .loop _ _ _ ss _ => ss.flatMap stmtAssumes
  | .ite _ ts es _ => ts.flatMap stmtAssumes ++ es.flatMap stmtAssumes
  | _ => []

/-- The assumptions of `p`'s bodies and its ground axioms. -/
private def learnedExprs (p : Core.Program) : List Core.Expression.Expr :=
  p.decls.flatMap fun
    | .proc q _ => match q.body with
      | .structured ss => ss.flatMap stmtAssumes
      | _ => []
    | .ax a _ => if a.e.hasBVar then [] else [a.e]
    | _ => []

/-- Every program of this file that type checks (all but `shadowDefPgm`). -/
private def allPrograms : List (String × StrataDDM.Program) :=
  [("literalPgm", (literalPgm : StrataDDM.Program)),
   ("constructorPgm", (constructorPgm : StrataDDM.Program)),
   ("applicationPgm", (applicationPgm : StrataDDM.Program)),
   ("booleanPgm", (booleanPgm : StrataDDM.Program)),
   ("coverPgm", (coverPgm : StrataDDM.Program)),
   ("residualPgm", (residualPgm : StrataDDM.Program)),
   ("unusedPgm", (unusedPgm : StrataDDM.Program)),
   ("foldFirstPgm", (foldFirstPgm : StrataDDM.Program)),
   ("foldAxiomsPgm", (foldAxiomsPgm : StrataDDM.Program)),
   ("axiomPgm", (axiomPgm : StrataDDM.Program)),
   ("conjunctionPgm", (conjunctionPgm : StrataDDM.Program)),
   ("definitionPgm", (definitionPgm : StrataDDM.Program)),
   ("opaqueEqPgm", (opaqueEqPgm : StrataDDM.Program)),
   ("depthPgm", (depthPgm : StrataDDM.Program)),
   ("shadowPgm", (shadowPgm : StrataDDM.Program)),
   ("axiomAfterPgm", (axiomAfterPgm : StrataDDM.Program)),
   ("contradictionPgm", (contradictionPgm : StrataDDM.Program)),
   ("unseenContradictionPgm", (unseenContradictionPgm : StrataDDM.Program)),
   ("undetectedBvPgm", (undetectedBvPgm : StrataDDM.Program)),
   ("undetectedQuantPgm", (undetectedQuantPgm : StrataDDM.Program)),
   ("lemmaPgm", (lemmaPgm : StrataDDM.Program)),
   ("lemmaOrderPgm", (lemmaOrderPgm : StrataDDM.Program)),
   ("lemmaContradictionPgm", (lemmaContradictionPgm : StrataDDM.Program)),
   ("lemmaQuantPgm", (lemmaQuantPgm : StrataDDM.Program)),
   ("vacuousQuantPgm", (vacuousQuantPgm : StrataDDM.Program)),
   ("noFactsQuantPgm", (noFactsQuantPgm : StrataDDM.Program)),
   ("mixedQuantPgm", (mixedQuantPgm : StrataDDM.Program)),
   ("nestedQuantPgm", (nestedQuantPgm : StrataDDM.Program)),
   ("positionsQuantPgm", (positionsQuantPgm : StrataDDM.Program)),
   ("absorbPgm", (absorbPgm : StrataDDM.Program)),
   ("anyAddressPgm", (anyAddressPgm : StrataDDM.Program)),
   ("positionsBvPgm", (positionsBvPgm : StrataDDM.Program)),
   ("literalRePgm", (literalRePgm : StrataDDM.Program)),
   ("factsRePgm", (factsRePgm : StrataDDM.Program)),
   ("encoderRejectedPgm", (encoderRejectedPgm : StrataDDM.Program)),
   ("longRePgm", (longRePgm : StrataDDM.Program)),
   ("connectivesPgm", (connectivesPgm : StrataDDM.Program)),
   ("connectivesDeadPgm", (connectivesDeadPgm : StrataDDM.Program)),
   ("connectivesPositionsPgm", (connectivesPositionsPgm : StrataDDM.Program)),
   ("connectivesRoundsPgm", (connectivesRoundsPgm : StrataDDM.Program)),
   ("connectivesLimitPgm", (connectivesLimitPgm : StrataDDM.Program)),
   ("connectivesGuardPgm", (connectivesGuardPgm : StrataDDM.Program)),
   ("noFactsPgm", (noFactsPgm : StrataDDM.Program)),
   ("hintPgm", (hintPgm : StrataDDM.Program)),
   ("positionsPgm", (positionsPgm : StrataDDM.Program)),
   ("hintScopePgm", (hintScopePgm : StrataDDM.Program)),
   ("polyHintPgm", (polyHintPgm : StrataDDM.Program)),
   ("hintProcPgm", (hintProcPgm : StrataDDM.Program)),
   ("undetectedPgm", (undetectedPgm : StrataDDM.Program)),
   ("hintFlowPgm", (hintFlowPgm : StrataDDM.Program)),
   ("hintLimitPgm", (hintLimitPgm : StrataDDM.Program))]

/-- Candidates recorded from `p`'s assumptions and ground axioms, and those of their key's
    type. -/
private def hintCount (p : Core.Program) : Except String (Nat × Nat) := do
  let F0 ← (Core.Transform.run p Core.Simplify.programFactory
    { Core.Transform.CoreTransformState.emp with factory := Core.Factory }).mapError toString
  let F := (Core.FoldAxioms.runCtx p F0).foldFactory
  let hs := (learnedExprs p).flatMap fun e =>
    (Core.EqualitySimplification.addAssumption F {} Core.EqualitySimplification.defDepth e).hints.toList
  let cands := hs.flatMap fun ((_, fty), vs) => vs.map (fty, ·)
  return (cands.length, (cands.filter fun (fty, v) => match fty with
    | .tcons "arrow" [ty, .tcons "bool" []] => Lambda.LExpr.typeCheck [] v == some ty
    | _ => false).length)

/--
info: candidates: 29 of 29 typed
-/
#guard_msgs in
#eval show IO Unit from do
  let mut c : Nat × Nat := (0, 0)
  for (name, p) in allPrograms do
    match (Core.typeCheck .quiet (parse p)).mapError (fun e => toString e.message) >>= hintCount with
    | .ok (a, b) => c := (c.1 + a, c.2 + b)
    | .error msg => IO.println s!"{name}: {msg}"
  IO.println s!"candidates: {c.2} of {c.1} typed"

open Core.EqualitySimplification.GoalsDefinedTest in
/-- Learning `assume f(x)`, with `x : bool` and `f : bool → bool`, records the candidate `x`,
    which `LExpr.typeCheck []` types at `bool` by its annotation. -/
private def varCandidate : Option (List Core.Expression.Expr) :=
  let x : Core.Expression.Expr := .fvar () ⟨"x", ()⟩ (some boolTy)
  let fs := Core.EqualitySimplification.addAssumption Core.Factory {}
    Core.EqualitySimplification.defDepth (.app () (.op () ⟨"f", ()⟩ (some (arr boolTy boolTy))) x)
  fs.hints.get? ("f", arr boolTy boolTy)

open Core.EqualitySimplification.GoalsDefinedTest in
#guard varCandidate == some [.fvar () ⟨"x", ()⟩ (some boolTy)] &&
  Lambda.LExpr.typeCheck [] (.fvar () ⟨"x", ()⟩ (some boolTy) : Core.Expression.Expr) == some boolTy

/-! ## Assumptions and ground axioms are typed by their own annotations

The theorems take as premise that the condition of each `assume`, and each ground axiom of
the program equality simplification runs on, is typed at `bool` by its own annotations
(`CmdOps`, `GroundAxiomsTyped`), so that the witness candidates learned from them are typed.
This counts them on every program of this file that type checks, as type checking leaves it
and after axiom folding. -/

/--
info: typed: 90 of 90, after axiom folding: 90 of 90
-/
#guard_msgs in
#eval show IO Unit from do
  let typed (p : Core.Program) : Nat × Nat :=
    let es := learnedExprs p
    (es.length, (es.filter fun e => Lambda.LExpr.typeCheck [] e == some .bool).length)
  let mut c₁ : Nat × Nat := (0, 0)
  let mut c₂ : Nat × Nat := (0, 0)
  for (name, p) in allPrograms do
    let r : Except String _ := do
      let prog ← (Core.typeCheck .quiet (parse p)).mapError (fun e => toString e.message)
      let st := { Core.Transform.CoreTransformState.emp with factory := Core.Factory }
      let (_, mid) ← (Core.Transform.run prog Core.FoldAxioms.runFoldAxioms st).mapError toString
      return (typed prog, typed mid)
    match r with
    | .ok (a, b) => c₁ := (c₁.1 + a.1, c₁.2 + a.2); c₂ := (c₂.1 + b.1, c₂.2 + b.2)
    | .error msg => IO.println s!"{name}: {msg}"
  IO.println s!"typed: {c₁.2} of {c₁.1}, after axiom folding: {c₂.2} of {c₂.1}"

open Core.EqualitySimplification.GoalsDefinedTest in
/-- `Bool.Not(x) == true` with `x` annotated `int`: it records the candidate `x` for
    `Bool.Not : bool → bool`, which is not typed at `bool`, and the typing premise excludes
    it, since the assumption itself is not typed by its own annotations. Evaluation reads
    `x`'s sort from the store, so where `x` holds the Boolean `false` the assumption is
    `true`. -/
private def mistypedAssume : Core.Expression.Expr :=
  .eq () (.app () (.op () ⟨"Bool.Not", ()⟩ (some (arr boolTy boolTy)))
    (.fvar () ⟨"x", ()⟩ (some intTy))) (.boolConst () true)

open Core.EqualitySimplification.GoalsDefinedTest in
#guard (Core.EqualitySimplification.addAssumption Core.Factory {}
    Core.EqualitySimplification.defDepth mistypedAssume).hints.get? ("Bool.Not", arr boolTy boolTy)
    == some [.fvar () ⟨"x", ()⟩ (some intTy)] &&
  Lambda.LExpr.typeCheck [] mistypedAssume == none

end Strata.EqualitySimplificationTest

end
