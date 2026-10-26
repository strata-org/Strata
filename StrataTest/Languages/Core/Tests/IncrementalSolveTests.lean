/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Languages.Core.IncrementalSolve
meta import Strata.Languages.Core.ObligationExtraction
meta import Strata.Transform.CommonSubexprElim
meta import Strata.Examples.EmbeddedData
meta import StrataDDM.Elab
meta import StrataDDM.BuiltinDialects.Init
import StrataDDM.Integration.Lean.HashCommands

meta section

/-! ## Walking a verification tree with long-lived solvers

Each test hands `Core.IncrementalSolve.verifyProgram` a program already in the
form `ObligationExtraction` accepts, so nothing upstream of the back end runs: no
`symbolicEval`, no call or loop elimination. That is the point of the harness. It
lets the solving side be exercised on its own, and it is why the programs below
are written with `assume`, `assert`, `var` and `if *` directly.

`verifyProgram p n` runs up to *n* solvers concurrently. Which goals each session checks is
decided before any solver starts, so a run reports every goal's session the same way every
time (`Trace.format`); the scheduling hook can only change when each result arrives, which
the tests below use to show that it changes nothing else.
-/

namespace Core.IncrementalSolve.Tests

open Strata

private def parse (p : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

/-- Report naming workers. Only used where the run has one worker or a scripted
    interleaving. -/
private def report (p : StrataDDM.Program) (sessions : Nat)
    (hook : Core.IncrementalSolve.Hook := Core.IncrementalSolve.noHook)
    (options : VerifyOptions := VerifyOptions.quiet)
    (wrapSolver : Strata.SMT.AbstractSolver Strata.SMT.Term Strata.SMT.TermType IO →
      Strata.SMT.AbstractSolver Strata.SMT.Term Strata.SMT.TermType IO := id) : IO Unit := do
  match ← Core.IncrementalSolve.verifyProgram (parse p) sessions options (hook := hook)
      (wrapSolver := wrapSolver) with
  | .ok (results, _, trace) => IO.println (trace.format results)
  | .error e => IO.println s!"error: {e}"

/-- Report of how the work fell out per node, and the workloads sorted. Independent of which
    worker reached which arm first, so a parallel run can be asserted on without scripting it. -/
private def shape (p : StrataDDM.Program) (sessions : Nat) : IO Unit := do
  match ← Core.IncrementalSolve.verifyProgram (parse p) sessions with
  | .ok (results, _, trace) => IO.println (trace.shape results)
  | .error e => IO.println s!"error: {e}"

/-- Report of what holds whatever order the solvers finish in. -/
private def invariants (p : StrataDDM.Program) (sessions : Nat) : IO Unit := do
  match ← Core.IncrementalSolve.verifyProgram (parse p) sessions with
  | .ok (results, _, trace) => IO.println (trace.invariants results)
  | .error e => IO.println s!"error: {e}"

/-- Wait until `p` holds, with a cap so a broken script fails in bounded time. -/
private def waitUntil (p : IO Bool) : IO Unit := do
  let mut n := 0
  while !(← p) && n < 20000 do
    IO.sleep 1
    n := n + 1

/-- Hold a worker until the script's next turn is its own, then consume that turn. Once the
    script runs out nobody waits, so the tail of a run is unscripted. Shared by both scripts
    below so the ordering they impose cannot drift apart. -/
private def awaitTurn (next : IO.Ref Nat) (seq : Array Nat) (worker : Nat) : IO Unit := do
  waitUntil do
    let k ← next.get
    return k ≥ seq.size || (seq.toList.drop k).head? == some worker
  let k ← next.get
  if k < seq.size then next.set (k + 1)

/-- Script the order in which workers take work: the `k`-th claim of the whole run
    goes to `seq[k]`, and once the script runs out the workers race as usual (by
    then there is nothing left to race for). Solvers still run concurrently; what
    is fixed is the order in which they finish, which is what a run would otherwise
    leave to chance. -/
private def scriptClaims (seq : Array Nat) : IO Core.IncrementalSolve.Hook := do
  let next ← IO.mkRef 0
  return fun ev worker _ => do
    match ev with
    | .beforeClaim => awaitTurn next seq worker
    | .afterCheck => pure ()

/-- `scriptClaims`, and additionally hold worker 0 after each of its checks until
    worker 1 has finished `target` of them. Forces the extreme split, where worker 1
    does all the work worker 0 has not started. -/
private def scriptClaimsAndHold (seq : Array Nat) (target : Nat) :
    IO Core.IncrementalSolve.Hook := do
  let next ← IO.mkRef 0
  let w1 ← IO.mkRef 0
  return fun ev worker _ => do
    match ev with
    | .beforeClaim => awaitTurn next seq worker
    | .afterCheck =>
      if worker == 1 then w1.modify (· + 1)
      else waitUntil (do return (← w1.get) ≥ target)

/-! ### One solver, three consecutive assertions, one context

The three assertions share `x` and the assumption about it. One solver is opened,
told those facts once, and asked three questions against them. `1 contexts` is
the claim under test: nothing was reset or re-declared between the assertions. -/

private def chainOfThree :=
#strata
program Core;

procedure P()
{
  var x : int;
  assume [pos]: int.gt(x, 0);
  assert [a1]: int.ge(x, 1);
  assert [a2]: int.gt(int.add(x, 1), 1);
  assert [a3]: int.ge(int.mul(x, 2), 2);
};
#end

/--
info: a1: session 0 proved
a2: session 0 proved
a3: session 0 proved
session 0: 3 checks, 1 contexts
-/
#guard_msgs in
#eval report chainOfThree 1

/-! ### A goal's own check leaves the next goal's context alone

Four goals on one node, checked in turn by one solver. Each is false, or reachable, under the
node's facts alone, and would read otherwise if an earlier check had been asserted rather than
assumed: `b` would be proved if `a`'s negation stayed, and `c` unreachable if `a` itself did.
Both solvers give every goal its own verdict. In deductive mode each `assert` is refuted. In
bug-finding mode an `assert` is also checked for satisfiability, so each reads satisfiable, that
is, it can hold and can fail; a leaked check would make one of them hold always or never. -/

private def checksLeaveNoTrace :=
#strata
program Core;

procedure P()
{
  var x : int;
  assert [a]: int.gt(x, 0);
  assert [b]: int.le(x, 0);
  cover [c]: int.le(x, 0);
  assert [d]: int.gt(x, 0);
};
#end

/--
info: cvc5 deductive: a ❌ fail, b ❌ fail, c ✅ pass, d ❌ fail
cvc5 bugFindingAssumingCompleteSpec: a ❓ satisfiable, b ❓ satisfiable, c ✅ pass, d ❓ satisfiable
z3 deductive: a ❌ fail, b ❌ fail, c ✅ pass, d ❌ fail
z3 bugFindingAssumingCompleteSpec: a ❓ satisfiable, b ❓ satisfiable, c ✅ pass, d ❓ satisfiable
-/
#guard_msgs in
#eval show IO Unit from do
  for solver in ["cvc5", "z3"] do
    for mode in [VerificationMode.deductive, VerificationMode.bugFindingAssumingCompleteSpec] do
      let options := { VerifyOptions.quiet with solver, checkMode := mode }
      match ← Core.IncrementalSolve.verifyProgram (parse checksLeaveNoTrace) 1 options with
      | .ok (results, _, _) =>
        let verdicts := results.toList.map fun r => s!"{r.obligation.label} {r.formatOutcome}"
        IO.println s!"{solver} {mode}: {", ".intercalate verdicts}"
      | .error e => IO.println s!"{solver} {mode}: error: {e}"

/-! ### Two assertions on one node, each with a symbol only it mentions

What a session has already told its solver is tracked by identity. Each goal here reaches
an uninterpreted function that no assumption on the path mentions and the sibling goal does
not use, so the second goal needs `g` declared while `f`, which the solver already holds,
must not be declared again.
-/

private def goalOnlySymbols :=
#strata
program Core;

function f(x: int): int;
function g(x: int): int;

procedure P()
{
  var x : int;
  assume [pos]: int.gt(x, 0);
  assert [usesF]: f(x) == f(x);
  assert [usesG]: g(x) == g(x);
};
#end

/--
info: usesF: session 0 proved
usesG: session 0 proved
session 0: 2 checks, 1 contexts
-/
#guard_msgs in
#eval report goalOnlySymbols 1

/-! ### A datatype over an opaque sort

Without array theory `Map` is an opaque sort, and `Box`'s constructor mentions it, so the
solver has to receive `Map`'s declaration before `Box`'s. -/

private def datatypeOverSort :=
#strata
program Core;

datatype Box () { MkBox(contents: Map int int) };

procedure P()
{
  var m : Map int int;
  var b : Box;
  assume [boxed]: b == MkBox(m);
  assert [sameBox]: b == MkBox(m);
};
#end

/--
info: sameBox: session 0 proved
session 0: 1 checks, 1 contexts
-/
#guard_msgs in
#eval report datatypeOverSort 1

/-! ### A procedure with one goal is sent in one shot

`single` holds one goal, so it shares a context with nothing and goes as one request, the way
the per-obligation path sends it. The other two are walked as trees. The results still come
back in the order the procedures are declared. -/

private def oneGoalBetweenTwo :=
#strata
program Core;

function f(x: int): int;

procedure before()
{
  var x : int;
  assume [pos]: int.gt(x, 0);
  assert [b1]: int.ge(x, 0);
  assert [b2]: f(x) == f(x);
};

procedure single()
{
  var y : int;
  assume [neg]: int.lt(y, 0);
  assert [s1]: int.lt(y, 1);
};

procedure after()
{
  var z : int;
  assert [a1]: z == z;
  assert [a2]: int.ge(z, z);
};
#end

/-- Verdicts and how many goals went in one shot, through the back-end seam. -/
private def throughSeam (p : StrataDDM.Program) : IO Unit := do
  let solver : Core.CoreSMTSolver := Core.IncrementalSolve.coreSMTSolver 1
  match ← (solver Core.Factory (parse p)).toIO' with
  | .ok (results, stats) =>
    for r in results do
      IO.println s!"{r.obligation.label}: {Core.IncrementalSolve.verdictOf r}"
    IO.println s!"one-shot goals: {stats.get "incremental.sentAlone"}"
  | .error e => IO.println s!"error: {e.format none}"

/--
info: b1: proved
b2: proved
s1: proved
a1: proved
a2: proved
one-shot goals: 1
-/
#guard_msgs in
#eval throughSeam oneGoalBetweenTwo

/-! ### A lemma is a goal under the axioms declared before it

A lemma is checked under the axioms before it and is never assumed, so `early` cannot use
the axiom declared after it, `late` can, and the procedure's goals do not assume either lemma.
Each lemma is a goal of the node it is declared at: `late` is a goal of the child the axiom
before it opens, so it shares the solver `early` was asked on, extended by that axiom. -/

private def lemmasAmongDecls :=
#strata
program Core;

const c : int;
axiom [cPos]: int.gt(c, 0);
lemma [early]: int.gt(c, 1);
axiom [cBig]: int.gt(c, 1);
lemma [late]: int.gt(c, 1);

procedure p()
{
  assert [p1]: int.gt(c, 0);
  assert [p2]: int.gt(c, 1);
};
#end

/--
info: early: REFUTED
late: proved
p1: proved
p2: proved
one-shot goals: 0
-/
#guard_msgs in
#eval throughSeam lemmasAmongDecls

/--
info: early: session 0 REFUTED
late: session 0 proved
p1: session 0 proved
p2: session 0 proved
session 0: 4 checks, 1 contexts
-/
#guard_msgs in
#eval report lemmasAmongDecls 1

/-! ### The lemmas of a program share a context

`l1` and `l2` follow one another, so they are goals of one node. The function after them opens a
child holding `l3`, so `l1` and `l2` are never checked by a solver holding its definition; the
axiom opens a child below that. Each child extends the context above it, so all four are asked
on one solver, and through the seam none of them goes in one shot. -/

private def consecutiveLemmas :=
#strata
program Core;

const c : int;
axiom [cPos]: int.gt(c, 0);
lemma [l1]: int.gt(c, 0);
lemma [l2]: int.ge(c, 1);
function twice(n : int) : int { int.mul(n, 2) }
lemma [l3]: int.gt(twice(c), 5);
axiom [cBig]: int.gt(c, 1);
lemma [afterAxiom]: int.gt(c, 1);
#end

/--
info: l1: session 0 proved
l2: session 0 proved
l3: session 0 REFUTED
afterAxiom: session 0 proved
session 0: 4 checks, 1 contexts
-/
#guard_msgs in
#eval report consecutiveLemmas 1

/--
info: l1: proved
l2: proved
l3: REFUTED
afterAxiom: proved
one-shot goals: 0
-/
#guard_msgs in
#eval throughSeam consecutiveLemmas

/-! ### A solver that fails costs only the goal it was solving

The checks numbered in `failing` (from 0) fail as a crashed process would. A solver that fails
after answering a check, as a remote session reaching its time limit would, is replaced and the
goal asked once more on the new one, so one such failure costs nothing. A failure on a solver
that had answered nothing yet, or a second one in a row, leaves that goal reporting it, and the
other goal is proved on a new solver, as the per-obligation path keeps a crash to the obligation
that met it. -/

private def checksFail (failing : List Nat) (p : StrataDDM.Program) : IO Unit := do
  let n ← IO.mkRef 0
  let wrap := fun (s : Strata.SMT.AbstractSolver Strata.SMT.Term Strata.SMT.TermType IO) =>
    { s with checkSatAssuming := fun lits => do
        if failing.contains (← n.modifyGet fun k => (k, k + 1)) then
          throw (IO.userError "solver process exited")
        s.checkSatAssuming lits }
  report p 1 (wrapSolver := wrap)

/--
info: usesF: session 0 proved
usesG: session 0 proved
session 0: 2 checks, 2 contexts
-/
#guard_msgs in
#eval checksFail [1] goalOnlySymbols

/--
info: usesF: session 0 error
usesG: session 0 proved
session 0: 1 checks, 2 contexts
-/
#guard_msgs in
#eval checksFail [0] goalOnlySymbols

/--
info: usesF: session 0 proved
usesG: session 0 error
session 0: 1 checks, 3 contexts
-/
#guard_msgs in
#eval checksFail [1, 2] goalOnlySymbols

/-! ### A check that runs out of time

cvc5 reports a per-check time limit as `unknown` and gives the reason only when asked. The
goal below is cubes summing to a cube, which cvc5 does not settle in a second, so it reports
a timeout, as the per-obligation path does. -/

private def outOfTime :=
#strata
program Core;

procedure P()
{
  var x : int;
  var y : int;
  var z : int;
  assume [big]: int.gt(x, 1) && int.gt(y, 1) && int.gt(z, 1);
  assert [noCubes]: !(int.add(int.mul(x, int.mul(x, x)), int.mul(y, int.mul(y, y)))
    == int.mul(z, int.mul(z, z)));
};
#end

/--
info: noCubes: session 0 timeout
session 0: 1 checks, 1 contexts
-/
#guard_msgs in
#eval report outOfTime 1 (options := { VerifyOptions.quiet with solverTimeout := 1 })

/-! ### The same three assertions, three solvers

Three workers on the same three assertions cost three contexts: each declares `x` and
asserts `pos` for itself before asking its question.

How the three divide between the workers depends on when each solver finishes, so
this asserts only what every interleaving satisfies. Checks equal to assertions is
the exactly-once property: no assertion was proved twice and none was skipped. -/

/--
info: 3 assertions, 3 checks, all proved: true
-/
#guard_msgs in
#eval invariants chainOfThree 3

/-! ### Three arms of a branch, two assertions each, three solvers

The arms' assumptions contradict one another, so no solver may hold two of them.

Each worker starts in its own arm and then takes that arm's second assertion, because
extending the path it holds costs it nothing while crossing to another arm costs a rebuild.
So the six assertions fall out as three arms of two, each proved by a single solver.

Which worker reaches which arm is a race: a worker that gets ahead does not wait politely,
and finding nothing left in its own arm it crosses into another and pays a rebuild. So the
arm assignment, the per-worker loads and the number of rebuilds are all timings, and this
scenario asserts none of them. What holds of every ordering is that the six assertions are
proved by six checks. -/

private def threeBranches :=
#strata
program Core;

procedure P()
{
  var x : int;
  assume [common]: int.gt(x, 0);
  if * {
    assume [lo]: int.lt(x, 10);
    assert [lo1]: int.lt(x, 11);
    assert [lo2]: int.le(x, 10);
  } else {
    if * {
      assume [mid]: int.ge(x, 10);
      assert [mid1]: int.ge(x, 9);
      assert [mid2]: int.gt(x, 8);
    } else {
      assume [hi]: int.ge(x, 100);
      assert [hi1]: int.ge(x, 99);
      assert [hi2]: int.gt(x, 98);
    }
  }
};
#end

/--
info: 6 assertions, 6 checks, all proved: true
-/
#guard_msgs in
#eval invariants threeBranches 3

/-! ### The same three arms, one solver

One worker takes all six assertions, which means it crosses both arm boundaries and
rebuilds to do it. -/

/--
info: 6 assertions, 6 checks, all proved: true
-/
#guard_msgs in
#eval invariants threeBranches 1

/-! ### What one arm assumed does not reach the next

The arms' assumptions contradict one another, so a solver still holding one arm's facts would
prove anything: an extra assumption never refutes a goal, it can only make a false one
provable. `hiNotLo` is false in its own arm, where `x` is at least 100, and would read proved
if `lo`, which says `x` is below 10, survived the reset between the sessions. Each arm is a
session of its own, and one worker takes the three in turn, so each arm after the first is
checked on the solver the previous arm used, after a reset. -/

private def threeBranchesOneFalse :=
#strata
program Core;

procedure P()
{
  var x : int;
  assume [common]: int.gt(x, 0);
  if * {
    assume [lo]: int.lt(x, 10);
    assert [lo1]: int.lt(x, 11);
    assert [lo2]: int.le(x, 10);
  } else {
    if * {
      assume [mid]: int.ge(x, 10);
      assert [mid1]: int.ge(x, 9);
      assert [mid2]: int.gt(x, 8);
    } else {
      assume [hi]: int.ge(x, 100);
      assert [hi1]: int.ge(x, 99);
      assert [hiNotLo]: int.lt(x, 10);
    }
  }
};
#end

/--
info: lo1: session 0 proved
lo2: session 0 proved
mid1: session 1 proved
mid2: session 1 proved
hi1: session 2 proved
hiNotLo: session 2 REFUTED
session 0: 2 checks, 1 contexts
session 1: 2 checks, 1 contexts
session 2: 2 checks, 1 contexts
-/
#guard_msgs in
#eval report threeBranchesOneFalse 1

/-! ### The same three arms, reported by shape

`Trace.shape` reports, per node, how many assertions sat there and how many distinct sessions
proved them, then the sessions' workloads sorted. Each arm is a run and so a session of its
own, even with one worker: three arms of two, each proved in one context, and the root
carrying nothing. -/

/--
info: node [0, 0]: 2 assertions, 1 solver(s)
node [0, 1, 0]: 2 assertions, 1 solver(s)
node [0, 1, 1]: 2 assertions, 1 solver(s)
workloads: 2 checks/1 contexts, 2 checks/1 contexts, 2 checks/1 contexts
-/
#guard_msgs in
#eval shape threeBranches 1

/-! ### Two solvers, one arm ten times the other: each keeps its own arm

The first arm holds ten assertions, the second holds one. They are two runs, since crossing
from one arm to the other starts the solver again, and two workers get one run each,
however unequal: the split is decided before either starts. Holding worker 0 after each of
its checks until worker 1 has finished one changes when worker 0's results arrive, and
nothing else: no session moves into the other's arm. -/

private def lopsided :=
#strata
program Core;

procedure P()
{
  var x : int;
  assume [common]: int.gt(x, 0);
  if * {
    assume [big]: int.gt(x, 100);
    assert [big1]: int.gt(x, 1);
    assert [big2]: int.gt(x, 2);
    assert [big3]: int.gt(x, 3);
    assert [big4]: int.gt(x, 4);
    assert [big5]: int.gt(x, 5);
    assert [big6]: int.gt(x, 6);
    assert [big7]: int.gt(x, 7);
    assert [big8]: int.gt(x, 8);
    assert [big9]: int.gt(x, 9);
    assert [big10]: int.gt(x, 10);
  } else {
    assume [small]: int.gt(x, 50);
    assert [small1]: int.gt(x, 1);
  }
};
#end

/--
info: big1: session 0 proved
big2: session 0 proved
big3: session 0 proved
big4: session 0 proved
big5: session 0 proved
big6: session 0 proved
big7: session 0 proved
big8: session 0 proved
big9: session 0 proved
big10: session 0 proved
small1: session 1 proved
session 0: 10 checks, 1 contexts
session 1: 1 checks, 1 contexts
-/
#guard_msgs in
#eval do report lopsided 2 (hook := ← scriptClaimsAndHold #[0, 1] 1)

/-! ### The same program, unscripted

Left to the solvers, the same split is checked: eleven checks for eleven assertions, and
everything is proved. -/

/--
info: 11 assertions, 11 checks, all proved: true
-/
#guard_msgs in
#eval invariants lopsided 2

/-! ### The split, before any solver starts

`planSessions` cuts the goals, in tree order, into the sessions the workers check, from the
tree and the session count alone. Each line is one session's goals.

- Every leaf starts a session, so one session and two give the same two sessions, however
  unequal.
- With more sessions asked for, the first session with the most goals is halved, the upper half
  holding the extra goal: three cut the big arm into five and five, four cut its first half again,
  into three and two.
- There are never more sessions than goals: twelve make eleven. -/

private def plan (p : StrataDDM.Program) (n : Nat) (byNode : Bool := false) : IO Unit := do
  match Core.IncrementalSolve.readProgram (parse p) with
  | .error e => IO.println s!"error: {e}"
  | .ok t =>
    let l := Core.IncrementalSolve.layoutOf t
    for ses in Core.IncrementalSolve.planSessions l n byNode do
      IO.println (" ".intercalate (ses.toList.filterMap fun g => l.tasks[g]?.map (·.goal.label)))

/--
info: big1 big2 big3 big4 big5 big6 big7 big8 big9 big10
small1
-/
#guard_msgs in
#eval plan lopsided 1

/--
info: big1 big2 big3 big4 big5 big6 big7 big8 big9 big10
small1
-/
#guard_msgs in
#eval plan lopsided 2

/--
info: big1 big2 big3 big4 big5
big6 big7 big8 big9 big10
small1
-/
#guard_msgs in
#eval plan lopsided 3

/--
info: big1 big2 big3
big4 big5
big6 big7 big8 big9 big10
small1
-/
#guard_msgs in
#eval plan lopsided 4

/--
info: big1
big2
big3
big4
big5
big6
big7
big8
big9
big10
small1
-/
#guard_msgs in
#eval plan lopsided 12

/-! With fewer sessions asked for than runs, each run is still a session: three arms make
three, whether one or two are asked for. -/

/--
info: lo1 lo2
mid1 mid2
hi1 hi2
-/
#guard_msgs in
#eval plan threeBranches 2

/-! Eight goals on the root and three leaves of one goal each. Asked for four sessions, the plan
cuts the root off its leaf and stops: one session of eight goals and three of one, four jobs that
start together. Each session asked for beyond that halves the largest: five cut the root's goals
into two sessions of four, seven into four sessions of two. -/

private def wideRootThinLeaves :=
#strata
program Core;

procedure P()
{
  var x : int;
  assume [pos]: int.gt(x, 0);
  assert [t1]: int.ge(x, 1);
  assert [t2]: int.ge(x, 0);
  assert [t3]: int.gt(x, int.neg(1));
  assert [t4]: int.ge(int.add(x, 1), 2);
  assert [t5]: int.gt(int.add(x, 1), 1);
  assert [t6]: int.ge(int.mul(x, 2), 2);
  assert [t7]: int.gt(int.mul(x, 2), 1);
  assert [t8]: int.ge(int.mul(x, 3), 3);
  if * {
    assert [l1]: int.ge(x, 1);
  } else {
    if * {
      assert [l2]: int.gt(x, 0);
    } else {
      assert [l3]: int.ge(x, 0);
    }
  }
};
#end

/--
info: t1 t2 t3 t4 t5 t6 t7 t8
l1
l2
l3
-/
#guard_msgs in
#eval plan wideRootThinLeaves 4

/--
info: t1 t2
t3 t4
t5 t6
t7 t8
l1
l2
l3
-/
#guard_msgs in
#eval plan wideRootThinLeaves 7

/--
info: t1 t2 t3 t4
t5 t6 t7 t8
l1
l2
l3
-/
#guard_msgs in
#eval plan wideRootThinLeaves 5

/-! Where a run is cut, the cut goes between two nodes when the bound of `⌈goals / workers⌉`
per session allows it, so a node's goals stay with one solver: here the two goals before
`more` and the three after it. -/

private def twoNodeChain :=
#strata
program Core;

procedure P()
{
  var x : int;
  assume [pos]: int.gt(x, 0);
  assert [a1]: int.ge(x, 1);
  assert [a2]: int.gt(x, 0);
  assume [more]: int.gt(x, 5);
  assert [b1]: int.ge(x, 6);
  assert [b2]: int.gt(x, 4);
  assert [b3]: int.gt(x, 3);
};
#end

/--
info: a1 a2
b1 b2 b3
-/
#guard_msgs in
#eval plan twoNodeChain 2

/-! Split by node, the same chain is two sessions even when one is asked for: each checks one
node's goals after sending its path, which is the shape of a request carrying a path and
several goals. Run that way, the second session sends `pos` and `more` before its three goals,
and each session uses one context. -/

/--
info: a1 a2
b1 b2 b3
-/
#guard_msgs in
#eval plan twoNodeChain 1 (byNode := true)

/-! Asked for more sessions than there are nodes, split by node still keeps each node's goals
together, so the plan is the same whatever the count. -/

/--
info: a1 a2
b1 b2 b3
-/
#guard_msgs in
#eval plan twoNodeChain 4 (byNode := true)

/--
info: a1: session 0 proved
a2: session 0 proved
b1: session 1 proved
b2: session 1 proved
b3: session 1 proved
session 0: 2 checks, 1 contexts
session 1: 3 checks, 1 contexts
-/
#guard_msgs in
#eval report twoNodeChain 1 (options := { VerifyOptions.quiet with splitByNode := true })

/-! Sessions grow from the leaves up, one node per turn. `r` is above both arms and `c1` and `c2`
above two leaves each. In the first turn the session of `a` takes `c1` and that of `d` takes
`c2`, and those of `b` and `e` find their parents taken; in the second the session of `a` takes
`r`. So the nodes shared by several leaves end up in different sessions, and each session is a
chain one solver walks without starting again. Asking for more sessions then halves the first
session holding the most nodes, `r c1 a`, upper half first, and then `r c1`. -/

private def twoLevels :=
#strata
program Core;

procedure P()
{
  var x : int;
  assert [r]: int.ge(x, x);
  if * {
    assume [h1]: int.gt(x, 0);
    assert [c1]: int.gt(x, int.neg(1));
    if * { assume [ha]: int.gt(x, 1); assert [a]: int.gt(x, 0); }
    else { assume [hb]: int.gt(x, 2); assert [b]: int.gt(x, 0); }
  } else {
    assume [h2]: int.lt(x, 0);
    assert [c2]: int.lt(x, 1);
    if * { assume [hd]: int.lt(x, int.neg(1)); assert [d]: int.lt(x, 0); }
    else { assume [he]: int.lt(x, int.neg(2)); assert [e]: int.lt(x, 0); }
  }
};
#end

/--
info: r c1 a
b
c2 d
e
-/
#guard_msgs in
#eval plan twoLevels 1

/--
info: r c1
a
b
c2 d
e
-/
#guard_msgs in
#eval plan twoLevels 5

/--
info: r
c1
a
b
c2 d
e
-/
#guard_msgs in
#eval plan twoLevels 6

/-! A tree of four nodes: `A` of 5 goals above `B` of 2 and `D` of 4, and `B` above `C`
of 2. The leaves `C` and `D` start two sessions, which take `B` and `A`. Both then hold two
nodes, so the one with more goals, `A D` with 9, is halved first, then `B C`. With every
session one node, `A`, of 5 goals, is halved into 3 and 2, and then `D` into 2 and 2. -/

private def docExample :=
#strata
program Core;

procedure P()
{
  var x : int;
  assert [a1]: int.ge(x, x);
  assert [a2]: int.le(x, x);
  assert [a3]: x == x;
  assert [a4]: int.ge(int.add(x, 1), x);
  assert [a5]: int.le(x, int.add(x, 1));
  if * {
    assume [hb]: int.gt(x, 0);
    assert [b1]: int.gt(x, int.neg(1));
    assert [b2]: int.ge(x, 1);
    assume [hc]: int.gt(x, 5);
    assert [c1]: int.gt(x, 4);
    assert [c2]: int.ge(x, 6);
  } else {
    assume [hd]: int.lt(x, 0);
    assert [d1]: int.lt(x, 1);
    assert [d2]: int.le(x, int.neg(1));
    assert [d3]: int.lt(x, 2);
    assert [d4]: int.le(x, 0);
  }
};
#end

/--
info: b1 b2 c1 c2
a1 a2 a3 a4 a5 d1 d2 d3 d4
-/
#guard_msgs in
#eval plan docExample 2

/--
info: b1 b2 c1 c2
a1 a2 a3 a4 a5
d1 d2 d3 d4
-/
#guard_msgs in
#eval plan docExample 3

/--
info: b1 b2
c1 c2
a1 a2 a3 a4 a5
d1 d2 d3 d4
-/
#guard_msgs in
#eval plan docExample 4

/--
info: b1 b2
c1 c2
a1 a2 a3
a4 a5
d1 d2 d3 d4
-/
#guard_msgs in
#eval plan docExample 5

/--
info: b1 b2
c1 c2
a1 a2 a3
a4 a5
d1 d2
d3 d4
-/
#guard_msgs in
#eval plan docExample 6

/-! Split by node, every node holding goals is a session of its own, whatever the count. -/

/--
info: r
c1
a
b
c2
d
e
-/
#guard_msgs in
#eval plan twoLevels 1 (byNode := true)

/-! ### The same verdicts and sessions on every run

Slowing one worker down changes when its results arrive, and running fewer solvers at once
changes which worker takes which session. Neither changes what a session checks: the plan
depends on the tree and the number of sessions alone, and each session starts on a fresh
solver. So the report, which names the session of every goal and counts each session's
checks and contexts, is the same in every run, whether one, two or four solvers run the four
sessions. -/

/-- A hook that holds `slow` for a moment after each of its checks. -/
private def delaying (slow : Nat) : Core.IncrementalSolve.Hook := fun ev worker _ =>
  if ev == .afterCheck && worker == slow then IO.sleep 20 else pure ()

private def sameEveryRun (p : StrataDDM.Program) (sessions : Nat) : IO Unit := do
  let options := { VerifyOptions.quiet with minSessions := some sessions }
  let mut seen : Array String := #[]
  for (n, hook) in [(sessions, Core.IncrementalSolve.noHook), (sessions, delaying 0),
      (sessions, delaying 1), (2, delaying 0), (1, Core.IncrementalSolve.noHook)] do
    match ← Core.IncrementalSolve.verifyProgram (parse p) n options (hook := hook) with
    | .ok (results, _, trace) => seen := seen.push (trace.format results)
    | .error e => seen := seen.push s!"error: {e}"
  IO.println s!"same in every run: {seen.all (· == seen.getD 0 "")}"
  IO.println (seen.getD 0 "")

/--
info: same in every run: true
lo1: session 0 proved
lo2: session 0 proved
mid1: session 1 proved
mid2: session 1 proved
hi1: session 2 proved
hi2: session 2 proved
session 0: 2 checks, 1 contexts
session 1: 2 checks, 1 contexts
session 2: 2 checks, 1 contexts
-/
#guard_msgs in
#eval sameEveryRun threeBranches 3

/--
info: same in every run: true
big1: session 0 proved
big2: session 0 proved
big3: session 0 proved
big4: session 1 proved
big5: session 1 proved
big6: session 2 proved
big7: session 2 proved
big8: session 2 proved
big9: session 2 proved
big10: session 2 proved
small1: session 3 proved
session 0: 3 checks, 1 contexts
session 1: 2 checks, 1 contexts
session 2: 5 checks, 1 contexts
session 3: 1 checks, 1 contexts
-/
#guard_msgs in
#eval sameEveryRun lopsided 4

/-! ### Boundaries: no assertions, and one assertion with no assumptions

Two degenerate programs, to pin the empty paths through `layoutOf`, `planSessions` and `run`.

A procedure with nothing to prove has an empty work list, so no session is planned and
no solver is started: the report is empty.

A single assertion with no assumption in front of it is the other end: the node's run
of facts is empty, so the goal is checked against a context holding only the prelude,
which is one check in one context. This is also the shape an `if *` arm takes when it
adds no facts of its own, which a producing phase is allowed to emit. -/

private def noAssertions :=
#strata
program Core;

procedure P()
{
  var x : int;
  assume [pos]: int.gt(x, 0);
};
#end

/--
info:
-/
#guard_msgs in
#eval report noAssertions 1

/-! ### A goal its own text settles is decided without a solver

`assert true` is decided the way the per-obligation path decides it, before anything is sent,
so the solver is asked only about `pos`. -/

private def trivialGoal :=
#strata
program Core;

procedure P()
{
  var x : int;
  assume [pos]: int.gt(x, 0);
  assert [obvious]: true;
  assert [pos2]: int.ge(x, 0);
};
#end

/--
info: obvious: session 0 proved
pos2: session 0 proved
session 0: 1 checks, 1 contexts
-/
#guard_msgs in
#eval report trivialGoal 1

/-! ### `--stop-on-first-error` stops taking goals after the first failure

`neg` is always false under `pos`, so it fails, and the run stops before checking `pos2`. That
goal is left out of the results, as the per-obligation loop leaves out what it never reached. -/

private def failsFirst :=
#strata
program Core;

procedure P()
{
  var x : int;
  assume [pos]: int.gt(x, 0);
  assert [neg]: int.lt(x, 0);
  assert [pos2]: int.ge(x, 0);
};
#end

/--
info: neg: session 0 REFUTED
session 0: 1 checks, 1 contexts
-/
#guard_msgs in
#eval report failsFirst 1
  (options := { Core.VerifyOptions.quiet with stopOnFirstError := true, checkLevel := .full })

/-! A goal decided without a solver stops the run too. The contradiction in the first arm decides
`reach`, a `cover` found unreachable, which is a failure; so the second arm's session is never
taken and `other` is left out. -/

private def deadCoverStops :=
#strata
program Core;

procedure P()
{
  var x : int;
  if * {
    assume [pos]: int.gt(x, 0);
    assume [neg]: int.lt(x, 0);
    assert [contradiction]: false;
    cover [reach]: int.gt(x, 1);
  } else {
    assert [other]: x == x;
  }
};
#end

/--
info: contradiction: session 0 proved
reach: session 0 unknown
session 0: 1 checks, 1 contexts
-/
#guard_msgs in
#eval report deadCoverStops 1
  (options := { Core.VerifyOptions.quiet with stopOnFirstError := true })

/--
info: 0 assertions, 0 checks, all proved: true
-/
#guard_msgs in
#eval invariants noAssertions 2

private def lonelyAssertion :=
#strata
program Core;

procedure P()
{
  assert [trivial]: int.gt(1, 0);
};
#end

/--
info: trivial: session 0 proved
session 0: 1 checks, 1 contexts
-/
#guard_msgs in
#eval report lonelyAssertion 1

/-! ### A refuted assertion comes back with a counterexample

The verdict of a check is the solver's `Decision`, because a counterexample, a timeout
and a give-up are three different answers and only one of them is a bug. This program
asserts something false, so the expected verdict is `REFUTED`.

The model is asserted only for its presence, not its text, since the exact
assignment a solver picks is its own business and varies between versions. Presence
is the part that matters: a reported counterexample is rendered into the message a
caller compares, so a `sat` with an empty model would report differently from a
`sat` with one. This is also what checks that model generation survived the way the
session launches its solver. -/

private def refutable :=
#strata
program Core;

procedure P()
{
  var x : int;
  assume [pos]: int.gt(x, 0);
  assert [wrong]: int.lt(x, 0);
};
#end

/-- Verdicts, and whether a counterexample came back with each. -/
private def verdicts (p : StrataDDM.Program) (sessions : Nat) : IO Unit := do
  match ← Core.IncrementalSolve.verifyProgram (parse p) sessions with
  | .ok (results, _, _) =>
    for r in results do
      -- The parsed model: the outcome carries what the rest of the pipeline reports, so an
      -- unparseable model shows up here as no counterexample.
      let cex := match r.outcome with
        | .ok o => match o.validityProperty with
          | .sat model => !model.isEmpty
          | _ => false
        | .error _ => false
      IO.println
        s!"{r.obligation.label}: {Core.IncrementalSolve.verdictOf r}, counterexample: {cex}"
  | .error e => IO.println s!"error: {e}"

/--
info: wrong: REFUTED, counterexample: true
-/
#guard_msgs in
#eval verdicts refutable 1

/-! ### A symbol reachable only from the goal is still declared

`f` appears in the assertion and in nothing else: no assumption on the path mentions
it. The context a session declares from therefore has to be the one the obligation
encoding returns, the only one that sees the goal's own symbols. Getting that wrong leaves the
solver with a reference to an undeclared `f`.

The axiom is what makes the goal provable, so a pass
here means `f` was declared, the axiom was sent, and the goal was checked against it. -/

private def goalOnlySymbol :=
#strata
program Core;

function f (x : int) : int;

axiom [fPos]: forall x : int :: int.gt(f(x), 0);

procedure P()
{
  var y : int;
  assume [ybound]: int.gt(y, 0);
  assert [fy]: int.gt(f(y), 0);
};
#end

/--
info: fy: session 0 proved
session 0: 1 checks, 1 contexts
-/
#guard_msgs in
#eval report goalOnlySymbol 1

/-! ### A fact after an assertion splits the node

`readStmts` closes a node when a fact arrives after an assertion, and continues as its child.
That is what keeps the later assumption out of scope for the earlier assertion, and it is the
only thing standing between the two: if the split did not happen, `a1` would be checked with
`extra` in scope.

`a1` is false under `pos` alone and holds under `extra`, so it reads refuted only if `extra`
was kept out of its check. One solver extends the root's context with the child's facts
without starting again, so both goals are checked in one context. -/

private def assumeAfterAssert :=
#strata
program Core;

procedure P()
{
  var x : int;
  assume [pos]: int.gt(x, 0);
  assert [a1]: int.ge(x, 11);
  assume [extra]: int.gt(x, 10);
  assert [a2]: int.ge(x, 11);
};
#end

/--
info: a1: session 0 REFUTED
a2: session 0 proved
session 0: 2 checks, 1 contexts
-/
#guard_msgs in
#eval report assumeAfterAssert 1

/-! ### A statement after an `if *` sees neither arm

A passive body does not put anything after an `if *`, but the extractor accepts it, so the
reader does too, as one more child of the same node. That child must see neither arm's facts.
`common` is false from `x`'s declaration alone, and would read proved if `lo`, or both arms,
leaked into it: `lo` says `x` is below 10, and the two arms together contradict each other, so
a solver holding both could prove anything. -/

private def afterBranch :=
#strata
program Core;

procedure P()
{
  var x : int;
  if * {
    assume [lo]: int.lt(x, 10);
    assert [lo1]: int.lt(x, 11);
  } else {
    assume [hi]: int.ge(x, 10);
    assert [hi1]: int.ge(x, 9);
  }
  assert [common]: int.lt(x, 11);
};
#end

/--
info: lo1: session 0 proved
hi1: session 1 proved
common: session 2 REFUTED
session 0: 1 checks, 1 contexts
session 1: 1 checks, 1 contexts
session 2: 1 checks, 1 contexts
-/
#guard_msgs in
#eval report afterBranch 1

/-! ### A `cover` is checked for satisfiability alone

`cover` is the other property `readStmts` admits, and it takes the opposite path through
`checksFor`: `passWhenUnreachable` is false for it, so in deductive mode it is checked for
satisfiability alone. That is why the validity column below reads `unknown`: it was never
asked. The check that did run asked whether `x` can exceed five
given only that it is positive, which it can.

The point of covering this branch is that the two properties must not be conflated: an
`assert` asks whether something always holds, a `cover` whether something can hold, and a
verifier that checked a `cover` for validity would report a reachable line as a failure. -/

private def withCover :=
#strata
program Core;

procedure P()
{
  var x : int;
  assume [pos]: int.gt(x, 0);
  cover [reachable]: int.gt(x, 5);
  assert [a1]: int.ge(x, 1);
};
#end

/--
info: reachable: session 0 unknown
a1: session 0 proved
session 0: 2 checks, 1 contexts
-/
#guard_msgs in
#eval report withCover 1

/-! ### A statement-level type declaration is refused

The tree reads exactly the programs `extractObligations` reads, and that path refuses a type
declared inside a body, so the tree refuses it too. -/

private def withLocalDecls :=
#strata
program Core;

procedure P()
{
  var x : int;
  assume [pos]: int.gt(x, 0);
  type Widget;
  assert [a1]: int.ge(x, 1);
  assert [a2]: int.ge(int.mul(x, 2), 2);
};
#end

/-- info: error: IncrementalSolve: unsupported statement in a passive body -/
#guard_msgs in
#eval report withLocalDecls 1

/-! ### Proving `false` decides everything below it

`pos` and `neg` contradict each other, so `contradiction` is valid, and its validity is the
solver's way of saying the facts on this path cannot all hold. Every goal that sees those facts
is then decided without a check: the solver would answer `unsat` to both questions for each of
them, so that is what they get. One check for four goals is the claim under test.

`reach` is the reason the outcome is recorded as two `unsat`s. A `cover`
is checked for satisfiability, and an unsatisfiable `cover` is unreachable, which is a failure:
reporting it as proved would hide a dead branch. -/

private def contradictoryFacts :=
#strata
program Core;

procedure P()
{
  var x : int;
  assume [pos]: int.gt(x, 0);
  assume [neg]: int.lt(x, 0);
  assert [contradiction]: false;
  assert [a1]: int.gt(x, 5);
  assert [a2]: int.lt(x, int.neg(5));
  cover [reach]: int.gt(x, 1);
};
#end

/-- Each goal's two check results, then the workers. -/
private def bothChecks (p : StrataDDM.Program) (sessions : Nat) : IO Unit := do
  let show_ : Core.SMT.Result → String
    | .unsat => "unsat" | .sat _ => "sat" | .unknown _ => "unknown" | .err _ => "error"
  match ← Core.IncrementalSolve.verifyProgram (parse p) sessions with
  | .ok (results, _, trace) =>
    for r in results do
      match r.outcome with
      | .ok o =>
        IO.println s!"{r.obligation.label}: satisfiable {show_ o.satisfiabilityProperty}, \
          valid {show_ o.validityProperty}"
      | .error _ => IO.println s!"{r.obligation.label}: error"
    for (name, checks, contexts) in trace.perSession do
      IO.println s!"session {name}: {checks} checks, {contexts} contexts"
  | .error e => IO.println s!"error: {e}"

/--
info: contradiction: satisfiable unknown, valid unsat
a1: satisfiable unknown, valid unsat
a2: satisfiable unknown, valid unsat
reach: satisfiable unsat, valid unknown
session 0: 1 checks, 1 contexts
-/
#guard_msgs in
#eval bothChecks contradictoryFacts 1

/-- How many checks reached the solver itself, counted by a wrapper around it. The engine's
    counter records the checks it meant to make; this records the ones the solver received, so it
    is what shows that the goals below the contradiction cost nothing. -/
private def solverChecks (p : StrataDDM.Program) (sessions : Nat) : IO Unit := do
  let calls ← IO.mkRef 0
  let wrap (s : Strata.SMT.AbstractSolver Strata.SMT.Term Strata.SMT.TermType IO) :=
    { s with
      checkSat := do calls.modify (· + 1); s.checkSat
      checkSatAssuming := fun lits => do calls.modify (· + 1); s.checkSatAssuming lits }
  match ← Core.IncrementalSolve.verifyProgram (parse p) sessions (wrapSolver := wrap) with
  | .ok (results, _, _) =>
    IO.println s!"{results.size} goals, {← calls.get} checks received by the solver"
  | .error e => IO.println s!"error: {e}"

/--
info: 4 goals, 1 checks received by the solver
-/
#guard_msgs in
#eval solverChecks contradictoryFacts 1

/-! ### A contradiction in one arm leaves the other arm to the solver

The facts of the first arm contradict each other and those of the second do not. Proving `false`
in the first arm decides `lo1` and nothing else: `hi1` sees none of the first arm's facts, so the
solver still has to check it. Two checks, then, one per arm, each arm being a session of its own. -/

private def contradictionInOneArm :=
#strata
program Core;

procedure P()
{
  var x : int;
  if * {
    assume [lo]: int.lt(x, 0);
    assume [alsoPos]: int.gt(x, 0);
    assert [dead]: false;
    assert [lo1]: int.gt(x, 100);
  } else {
    assume [hi]: int.ge(x, 10);
    assert [hi1]: int.ge(x, 9);
  }
};
#end

/--
info: dead: session 0 proved
lo1: session 0 proved
hi1: session 1 proved
session 0: 1 checks, 1 contexts
session 1: 1 checks, 1 contexts
-/
#guard_msgs in
#eval report contradictionInOneArm 1

/-! ### Pruning sends each goal the axioms the per-obligation path keeps for it

Each goal needs one of the two axioms. With pruning off, both axioms sit at the root, so the
solver is told both and proves the two goals in one context.

With pruning on, a goal is sent only the axioms its pruning keeps and the solver lacks. Under
the default, lazy pruning, the first goal is told `fPos` alone, which is exactly the per-obligation
path's question, and the second is told `gNeg` on top of it: one context, each axiom sent once,
and the second goal also sees `fPos`, which its own pruning drops.

Exact pruning does not let it: the second goal drops `fPos`, which a solver cannot take back, so
the solver starts again and is told `gNeg` alone. Two contexts is the evidence that nothing was
shared that a goal's pruning drops. -/

private def twoAxioms :=
#strata
program Core;

function f(x: int): int;
function g(x: int): int;
axiom [fPos]: forall x : int :: int.gt(f(x), 0);
axiom [gNeg]: forall x : int :: int.lt(g(x), 0);

procedure P()
{
  var y : int;
  assert [usesF]: int.gt(f(y), 0);
  assert [usesG]: int.lt(g(y), 0);
};
#end

/-- Verdicts, then contexts built and asserts received by the solver, under a pruning mode. -/
private def withPruning (p : StrataDDM.Program) (mode : Core.IrrelevantAxiomsMode)
    (exact : Bool := false) : IO Unit := do
  let asserts ← IO.mkRef 0
  let wrap (s : Strata.SMT.AbstractSolver Strata.SMT.Term Strata.SMT.TermType IO) :=
    { s with assert := fun t => do asserts.modify (· + 1); s.assert t }
  let options := { Core.VerifyOptions.quiet with removeIrrelevantAxioms := mode,
                                                 exactPruning := exact }
  match ← Core.IncrementalSolve.verifyProgram (parse p) 1 options (wrapSolver := wrap) with
  | .ok (results, _, trace) =>
    for r in results do
      IO.println s!"{r.obligation.label}: {Core.IncrementalSolve.verdictOf r}"
    let contexts := trace.perSession.foldl (fun a (_, _, c) => a + c) 0
    IO.println s!"{contexts} contexts, {← asserts.get} asserts"
  | .error e => IO.println s!"error: {e}"

/--
info: usesF: proved
usesG: proved
1 contexts, 2 asserts
-/
#guard_msgs in
#eval withPruning twoAxioms .Off

/--
info: usesF: proved
usesG: proved
1 contexts, 2 asserts
-/
#guard_msgs in
#eval withPruning twoAxioms .Aggressive

/--
info: usesF: proved
usesG: proved
2 contexts, 2 asserts
-/
#guard_msgs in
#eval withPruning twoAxioms .Aggressive (exact := true)

/-! ### z3 reports a per-check time limit as a timeout too

Started with `-t:`, z3 answers a check it abandons with `unknown`, and gives the reason only
when asked, as `canceled`. Ten pigeons do not fit in nine holes: each `x` is a pigeon's hole, and
no two share one. z3 does not settle that in a second, so the goal reports a timeout, as it does
under cvc5. -/

private def pigeonhole :=
#strata
program Core;

procedure P()
{
  var x0 : int; var x1 : int; var x2 : int; var x3 : int; var x4 : int;
  var x5 : int; var x6 : int; var x7 : int; var x8 : int; var x9 : int;
  assume [hole0]: int.ge(x0, 0) && int.lt(x0, 9);
  assume [hole1]: int.ge(x1, 0) && int.lt(x1, 9);
  assume [hole2]: int.ge(x2, 0) && int.lt(x2, 9);
  assume [hole3]: int.ge(x3, 0) && int.lt(x3, 9);
  assume [hole4]: int.ge(x4, 0) && int.lt(x4, 9);
  assume [hole5]: int.ge(x5, 0) && int.lt(x5, 9);
  assume [hole6]: int.ge(x6, 0) && int.lt(x6, 9);
  assume [hole7]: int.ge(x7, 0) && int.lt(x7, 9);
  assume [hole8]: int.ge(x8, 0) && int.lt(x8, 9);
  assume [hole9]: int.ge(x9, 0) && int.lt(x9, 9);
  assume [alone0]: !(x0 == x1) && !(x0 == x2) && !(x0 == x3) && !(x0 == x4) && !(x0 == x5)
    && !(x0 == x6) && !(x0 == x7) && !(x0 == x8) && !(x0 == x9);
  assume [alone1]: !(x1 == x2) && !(x1 == x3) && !(x1 == x4) && !(x1 == x5) && !(x1 == x6)
    && !(x1 == x7) && !(x1 == x8) && !(x1 == x9);
  assume [alone2]: !(x2 == x3) && !(x2 == x4) && !(x2 == x5) && !(x2 == x6) && !(x2 == x7)
    && !(x2 == x8) && !(x2 == x9);
  assume [alone3]: !(x3 == x4) && !(x3 == x5) && !(x3 == x6) && !(x3 == x7) && !(x3 == x8)
    && !(x3 == x9);
  assume [alone4]: !(x4 == x5) && !(x4 == x6) && !(x4 == x7) && !(x4 == x8) && !(x4 == x9);
  assume [alone5]: !(x5 == x6) && !(x5 == x7) && !(x5 == x8) && !(x5 == x9);
  assume [alone6]: !(x6 == x7) && !(x6 == x8) && !(x6 == x9);
  assume [alone7]: !(x7 == x8) && !(x7 == x9);
  assume [alone8]: !(x8 == x9);
  assert [php]: false;
};
#end

/--
info: php: session 0 timeout
session 0: 1 checks, 1 contexts
-/
#guard_msgs in
#eval report pigeonhole 1
  (options := { VerifyOptions.quiet with solver := "z3", solverTimeout := 1 })

/-! ### A refuted goal carries its counterexample in the result

The model is what the result reports, so it is checked where a caller reads it. -/

/--
info: wrong: counterexample reported: true
-/
#guard_msgs in
#eval do
  match ← Core.IncrementalSolve.verifyProgram (parse refutable) 1 with
  | .ok (results, _, _) =>
    for r in results do
      IO.println s!"{r.obligation.label}: counterexample reported: {!r.lexprModel.isEmpty}"
  | .error e => IO.println s!"error: {e}"

/-! ### A solver that dies between checks is replaced

The solver's first reset fails, as a process that exited after its last answer would. The
worker starts a new solver, so the second arm is still proved. -/

private def twoArms :=
#strata
program Core;

procedure P()
{
  var x : int;
  if * {
    assume [pos]: int.gt(x, 0);
    assert [p1]: int.ge(x, 0);
  } else {
    assume [neg]: int.lt(x, 0);
    assert [n1]: int.le(x, 0);
  }
};
#end

private def firstResetFails (p : StrataDDM.Program) : IO Unit := do
  let failed ← IO.mkRef false
  let wrap := fun (s : Strata.SMT.AbstractSolver Strata.SMT.Term Strata.SMT.TermType IO) =>
    { s with reset := do
        if !(← failed.get) then
          failed.set true
          throw (IO.userError "solver process exited")
        s.reset }
  report p 1 (wrapSolver := wrap)

/--
info: p1: session 0 proved
n1: session 1 proved
session 0: 1 checks, 1 contexts
session 1: 1 checks, 1 contexts
-/
#guard_msgs in
#eval firstResetFails twoArms

/-! ### `--stop-on-first-error` stops the one-shot half too

`a1` fails in a procedure walked as a tree, so the procedure holding the single goal `b1` is
never sent, as the per-obligation loop would stop after `a1`. -/

private def failsBeforeLone :=
#strata
program Core;

procedure A()
{
  var x : int;
  assume [pos]: int.gt(x, 0);
  assert [a1]: int.lt(x, 0);
  assert [a2]: int.ge(x, 0);
};

procedure B()
{
  var y : int;
  assume [pos]: int.gt(y, 0);
  assert [b1]: int.lt(y, 0);
};
#end

/--
info: a1: REFUTED
-/
#guard_msgs in
#eval do
  let options := { Core.VerifyOptions.quiet with stopOnFirstError := true }
  let solver : Core.CoreSMTSolver := Core.IncrementalSolve.coreSMTSolver 1 options
  match ← (solver Core.Factory (parse failsBeforeLone)).toIO' with
  | .ok (results, _) =>
    for r in results do
      IO.println s!"{r.obligation.label}: {Core.IncrementalSolve.verdictOf r}"
  | .error e => IO.println s!"error: {e.format none}"

/-! ### A goal sent alone is asked its own question, whatever shares its label

`L` is asserted twice. The copy in the first arm shares its session with `usesF`, which keeps the
false axiom `bad`, and lazy pruning leaves it to `L`, which the walk then proves. The copy in the
second arm is a session of one, sent alone: it is asked its own obligation, which drops `bad`,
and is refuted, whatever the other copy of `L` got. Under `--stop-on-first-error` that refutation
stops the run, which so reports the failure. -/

private def labelSharedWithWalked :=
#strata
program Core;

function f(x: int): int;
axiom [bad]: f(0) == 1 && f(0) == 2;

procedure P()
{
  var x : int;
  if * {
    assert [usesF]: f(x) == f(x);
    assert [L]: int.lt(x, 0);
  } else {
    assert [L]: int.lt(x, 0);
  }
};
#end

/--
info: usesF: proved
L: proved
L: REFUTED
-/
#guard_msgs in
#eval do
  let options := { Core.VerifyOptions.quiet with stopOnFirstError := true,
                                                 removeIrrelevantAxioms := .Aggressive }
  let solver : Core.CoreSMTSolver := Core.IncrementalSolve.coreSMTSolver 1 options
  match ← (solver Core.Factory (parse labelSharedWithWalked)).toIO' with
  | .ok (results, _) =>
    for r in results do
      IO.println s!"{r.obligation.label}: {Core.IncrementalSolve.verdictOf r}"
  | .error e => IO.println s!"error: {e.format none}"

/-! ### A goal a shared context leaves unknown is reported unknown

The second check a solver is asked answers `unknown`, as a solver that lost its way in a context
earlier goals shaped might. `excl` is that second check, and the session's answer is the one
reported: a goal meant to be checked on its own can be made a session of its own. -/

private def twoGoals :=
#strata
program Core;

procedure P()
{
  var x : int;
  assume [pos]: int.gt(x, 0);
  assert [fair]: int.ge(x, 0);
  assert [excl]: int.ge(x, 1);
};
#end

private def secondCheckUnknown (p : StrataDDM.Program) : IO Unit := do
  let calls ← IO.mkRef (0 : Nat)
  let wrap := fun (s : Strata.SMT.AbstractSolver Strata.SMT.Term Strata.SMT.TermType IO) =>
    { s with checkSatAssuming := fun lits => do
        calls.modify (· + 1)
        if (← calls.get) == 2 then pure .unknown else s.checkSatAssuming lits }
  match ← Core.IncrementalSolve.verifyProgram (parse p) 1 (wrapSolver := wrap) with
  | .ok (results, _, trace) =>
    IO.println (trace.format results)
  | .error e => IO.println s!"error: {e}"

/--
info: fair: session 0 proved
excl: session 0 unknown
session 0: 2 checks, 1 contexts
-/
#guard_msgs in
#eval secondCheckUnknown twoGoals

/-! ### A failure right after a rebuild is still the solver's

The second check below, the first in the other arm after the context is rebuilt, fails. The
solver had answered a check before the rebuild, so the failure is the solver's: it is replaced
and the goal asked again, and both are proved. -/

/--
info: p1: session 0 proved
n1: session 1 proved
session 0: 1 checks, 1 contexts
session 1: 1 checks, 2 contexts
-/
#guard_msgs in
#eval checksFail [1] twoArms

/-- A session on a local cvc5, started the way the tree starts one, for the factories below. -/
private def localCvc5 (options : VerifyOptions) :
    IO (Strata.SMT.AbstractSolver Strata.SMT.Term Strata.SMT.TermType IO) := do
  let st ← Strata.SMT.IncrementalSolver.spawn "cvc5"
    #["--quiet", "--lang", "smt", "--incremental", "--produce-models",
      s!"--tlimit-per={options.solverTimeout * 1000}"]
  return Core.IncrementalSolve.raisingIn
    (Strata.SMT.IncrementalSolver.mkIncrementalSolver st) (← IO.mkRef none)

/-! ### A replacement that cannot be started costs only the goal it was for

Sessions here come from a factory over local cvc5. The first session's first check fails, and
the factory then refuses three sessions, more than a replacement waits for, before it starts
them again. The goal that met the failure reports it, and the worker replaces its session on
the next goal, which is proved. -/

private def refusedReplacements (p : StrataDDM.Program) : IO Unit := do
  let spawns ← IO.mkRef (0 : Nat)
  let checks ← IO.mkRef (0 : Nat)
  let factory : Core.IncrementalSolve.SessionFactory :=
    { τ := Strata.SMT.Term, σ := Strata.SMT.TermType
      spawn := fun options => do
        let n ← spawns.modifyGet fun n => (n, n + 1)
        if 1 ≤ n && n ≤ 3 then throw (IO.userError "session refused")
        let s ← localCvc5 options
        pure { s with checkSatAssuming := fun lits => do
          if (← checks.modifyGet fun c => (c, c + 1)) == 0 then
            throw (IO.userError "session closed")
          s.checkSatAssuming lits } }
  match ← Core.IncrementalSolve.verifyProgramWith factory (parse p) 1 with
  | .ok (results, _, _) =>
    for r in results do IO.println s!"{r.obligation.label}: {Core.IncrementalSolve.verdictOf r}"
  | .error e => IO.println s!"error: {e}"

/--
info: fair: error
excl: proved
-/
#guard_msgs in
#eval refusedReplacements twoGoals

/-! ### Sessions of one goal go through the per-obligation discharge

A session holding one goal shares nothing, so it is not walked on a solver of its own: with
twelve sessions asked for, the eleven goals of `lopsided` are eleven sessions of one goal, and
each is sent through the per-obligation discharge by the worker that takes it, which a remote
backend sends as a single request and a local solver answers on a live solver. With one session
per arm, only `small1` is alone. -/

private def sentAlone (p : StrataDDM.Program) (minSessions : Nat) (remote : Bool) : IO Unit := do
  let options := { VerifyOptions.quiet with minSessions := some minSessions }
  let factory : Core.IncrementalSolve.SessionFactory :=
    { τ := Strata.SMT.Term, σ := Strata.SMT.TermType, spawn := localCvc5 }
  let solver : Core.CoreSMTSolver := Core.IncrementalSolve.coreSMTSolver 2 options
    (session := if remote then some factory else none)
  match ← (solver Core.Factory (parse p)).toIO' with
  | .ok (results, stats) =>
    let proved := results.all fun r => Core.IncrementalSolve.verdictOf r == "proved"
    let alone := stats.get "incremental.sentAlone"
    IO.println s!"all proved: {proved}, sent alone: {alone}"
  | .error e => IO.println s!"error: {e.format none}"

/-- info: all proved: true, sent alone: 11 -/
#guard_msgs in
#eval sentAlone lopsided 12 (remote := true)

/-- info: all proved: true, sent alone: 1 -/
#guard_msgs in
#eval sentAlone lopsided 2 (remote := true)

/-- info: all proved: true, sent alone: 11 -/
#guard_msgs in
#eval sentAlone lopsided 12 (remote := false)

/-! ### A refusal between two sessions does not end the worker

One worker runs two sessions, one per procedure. Its solver can never be reset, so between the
sessions it is replaced, and the factory refuses the next four sessions, more than a patient
replacement tries. The worker is not ended by that: it goes on to the second session, which
replaces the solver again once the refusal is over, and every goal is proved. The counts show
the refusals happened: six sessions asked for, four refused. -/

private def twoProcedures :=
#strata
program Core;

procedure P()
{
  var x : int;
  assume [pos]: int.gt(x, 0);
  assert [p1]: int.ge(x, 0);
  assert [p2]: int.gt(x, int.neg(1));
};

procedure Q()
{
  var y : int;
  assume [neg]: int.lt(y, 0);
  assert [q1]: int.le(y, 0);
  assert [q2]: int.lt(y, 1);
};
#end

private def refusedBetweenSessions (p : StrataDDM.Program) : IO Unit := do
  let spawns ← IO.mkRef (0 : Nat)
  let resets ← IO.mkRef (0 : Nat)
  let factory : Core.IncrementalSolve.SessionFactory :=
    { τ := Strata.SMT.Term, σ := Strata.SMT.TermType
      spawn := fun options => do
        let n ← spawns.modifyGet fun n => (n, n + 1)
        if 1 ≤ n && n ≤ 4 then throw (IO.userError "session refused")
        let s ← localCvc5 options
        pure { s with reset := do resets.modify (· + 1); throw (IO.userError "reset failed") } }
  match ← Core.IncrementalSolve.verifyProgramWith factory (parse p) 1 with
  | .ok (results, _, _) =>
    for r in results do IO.println s!"{r.obligation.label}: {Core.IncrementalSolve.verdictOf r}"
    IO.println s!"resets tried: {← resets.get}, sessions asked for: {← spawns.get}"
  | .error e => IO.println s!"error: {e}"

/--
info: p1: proved
p2: proved
q1: proved
q2: proved
resets tried: 2, sessions asked for: 6
-/
#guard_msgs in
#eval refusedBetweenSessions twoProcedures

/-! ### A caller's own discharge without sessions serves every goal

A caller that passes its own discharge decides where queries go: without sessions of its own,
`--incremental` does not walk the tree with local solver processes, and every goal, the two in
one procedure included, goes through that discharge. -/

private def countedDischarge (p : StrataDDM.Program) : IO Unit := do
  let calls ← IO.mkRef (0 : Nat)
  let mk : Core.MkDischargeFn := fun _ _ _ _ _ _ _ _ _ =>
    fun _ _ _ _ _ _ _ => do
      calls.modify (· + 1)
      pure (.ok (.unsat, .unsat, Strata.SMT.EncoderState.init))
  match ← (Strata.Core.verifyProgram (parse p)
      { VerifyOptions.quiet with solver := "not-a-local-solver", incremental := true }
      (mkDischarge := mk)).toBaseIO with
  | .ok results =>
    for r in results do IO.println s!"{r.obligation.label}: {verdictOf r}"
    IO.println s!"discharge calls: {← calls.get}"
  | .error e => IO.println s!"error: {e}"

/--
info: fair: proved
excl: proved
discharge calls: 2
-/
#guard_msgs in
#eval countedDischarge twoGoals

/-! A goal sent alone goes to the per-obligation discharge with the caller's worker count. Under
`--parallel` several workers send goals at once, and a back end that shares one connection
between the obligations of a sequential run learns that it must not from that count. -/

/-- info: s1: proved; worker counts the discharge saw: [3] -/
#guard_msgs in
#eval show IO Unit from do
  let seen ← IO.mkRef (#[] : Array Nat)
  let mk : Core.MkDischargeFn := fun options _ _ _ _ _ _ _ _ =>
    fun _ _ _ _ _ _ _ => do
      seen.modify fun a => if a.contains options.parallelWorkers then a
        else a.push options.parallelWorkers
      pure (.ok (.unsat, .unsat, Strata.SMT.EncoderState.init))
  let options := { VerifyOptions.quiet with parallelWorkers := 3 }
  let solver : Core.CoreSMTSolver :=
    Core.IncrementalSolve.coreSMTSolver 3 options (mkDischarge := mk)
  match ← (solver Core.Factory (parse oneGoalBetweenTwo)).toBaseIO with
  | .ok (results, _) =>
    let lone := results.toList.filter (·.obligation.label == "s1")
    let verdicts := lone.map fun r => s!"{r.obligation.label}: {verdictOf r}"
    let counts := (← seen.get).toList
    IO.println s!"{"; ".intercalate verdicts}; worker counts the discharge saw: {counts}"
  | .error e => IO.println s!"error: {e.format none}"

/-! ### A function's body reads its own parameters

Two defined functions share a parameter name. Each body has to read its own parameter, not
a constant declared for the first function's parameter and renamed for the second, which would
leave `twice` returning the same value whatever its argument. -/

private def sharedParamName :=
#strata
program Core;
function inc(n : int) : int { int.add(n, 1) }
function twice(n : int) : int { int.mul(n, 2) }
procedure P()
{
  assert [inc_one]: inc(1) == 2;
  assert [twice_three]: twice(3) == 6;
};
#end

/--
info: inc_one: session 0 proved
twice_three: session 0 proved
session 0: 2 checks, 1 contexts
-/
#guard_msgs in
#eval report sharedParamName 1

/-! ### Parameters named like a function, and contracts

A pipeline that runs `simplify` in place of symbolic evaluation leaves procedures their
parameters. A parameter named like a function is then renamed apart, so `c == 5` is a question
about the argument, which `ax` says nothing about: both goals are refuted. A procedure
that still has a contract is refused, as by `extractObligations`. -/

private def paramNamedLikeFunction :=
#strata
program Core;
function c() : int;
axiom [ax]: c() == 5;
procedure P (c : int) { assert [g]: c == 5; assert [g2]: c == 5; };
#end

private def withContract :=
#strata
program Core;
procedure P (x : int)
spec { requires [pre]: int.gt(x, 0); }
{ assert [g]: int.gt(x, 0); assert [g2]: int.ge(x, 0); };
#end

/-! ### The tree reads the obligations the per-obligation path reads

Every verdict here is meant to be the per-obligation one, and that rests on the tree holding
exactly the obligations `extractObligations` finds: the same labels, properties and goals, in
the same order, each under the same assumptions in the same order. Rebuilding each goal's
obligation from the tree and comparing it with the extracted one checks that on every program
in this file. -/

private def sameObligations (programs : List (String × StrataDDM.Program)) : IO Unit := do
  for (name, sp) in programs do
    let p := parse sp
    let render (o : Imperative.ProofObligation Expression) : String :=
      s!"{o.label} {Std.format o.property}: {Std.format o.assumptions} ⊢ {Std.format o.obligation}"
    match readProgram p, Core.ObligationExtraction.extractObligations p with
    | .ok tree, .ok obs =>
      let fromTree := (layoutOf tree).tasks.toList.map (render ∘ obligationOf)
      let extracted := obs.toList.map render
      unless fromTree == extracted do
        IO.println s!"{name} differs:\n  tree: {fromTree}\n  extracted: {extracted}"
    | .error _, .error _ => pure ()
    | .error e, _ => IO.println s!"{name}: only the tree fails: {e}"
    | _, .error e => IO.println s!"{name}: only extraction fails: {e}"
  IO.println s!"{programs.length} programs agree"

/-- info: 30 programs agree -/
#guard_msgs in
#eval sameObligations [("chainOfThree", chainOfThree), ("goalOnlySymbols", goalOnlySymbols),
  ("datatypeOverSort", datatypeOverSort), ("oneGoalBetweenTwo", oneGoalBetweenTwo),
  ("lemmasAmongDecls", lemmasAmongDecls), ("outOfTime", outOfTime),
  ("threeBranches", threeBranches), ("lopsided", lopsided), ("noAssertions", noAssertions),
  ("trivialGoal", trivialGoal), ("failsFirst", failsFirst), ("deadCoverStops", deadCoverStops),
  ("lonelyAssertion", lonelyAssertion), ("refutable", refutable),
  ("goalOnlySymbol", goalOnlySymbol), ("assumeAfterAssert", assumeAfterAssert),
  ("afterBranch", afterBranch), ("withCover", withCover), ("withLocalDecls", withLocalDecls),
  ("contradictoryFacts", contradictoryFacts), ("contradictionInOneArm", contradictionInOneArm),
  ("twoAxioms", twoAxioms), ("pigeonhole", pigeonhole), ("twoArms", twoArms),
  ("failsBeforeLone", failsBeforeLone), ("twoGoals", twoGoals),
  ("sharedParamName", sharedParamName), ("consecutiveLemmas", consecutiveLemmas),
  ("paramNamedLikeFunction", paramNamedLikeFunction), ("withContract", withContract)]

/-! ### `--incremental` gives the per-obligation results through the whole pipeline

`Core.verifyProgram` with `incremental` off and on, over the shipped examples that verify and
over programs of this file, in each check mode, compares the full results: verdicts, the
diagnoses that follow from them, and counterexample models. -/

/-- Parse the text of a Core program. -/
private def parseText (text : String) : IO Core.Program := do
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[StrataDDM.initDialect, Strata.Core]
  let body := if text.startsWith "program Core;" then (text.drop "program Core;".length).toString
    else text
  let sp ← StrataDDM.Elab.parseStrataProgramFromDialect dialects "Core"
    (StrataDDM.Parser.stringInputContext ⟨"example"⟩ body)
  pure (parse sp)

/-- Run `p` through the whole pipeline with `--incremental` off and on, and compare each result,
    its verdict and its counterexample. The counterexample is compared as it is reported, the
    variables and their values, which `Std.format` of a result leaves out below `--models`.

    The pipeline leaves each branch of a procedure a single assertion, so with `--incremental`
    every goal is a session of one and is sent the per-obligation way. `walkAll` walks them
    instead, so what is compared is the walk itself. -/
private def bothWays (name : String) (p : Core.Program) (options : VerifyOptions)
    (pipeline : Option (Core.ValidatedPipeline Core.ProgramFactSet.empty) := none)
    (walkAll : Bool := false) : IO Unit := do
  let run (incremental : Bool) :=
    let options := { options with incremental }
    let solver := if incremental && walkAll then
        some (Core.IncrementalSolve.coreSMTSolver options.parallelWorkers options
          (axiomProgram := some p) (sendAlone := false))
      else none
    (Strata.Core.verifyProgram p options (pipeline := pipeline) (solver := solver)).toBaseIO
  let render (r : Core.VCResult) := s!"{Std.format r}{if r.lexprModel.isEmpty then ""
    else s!" model {Std.format r.lexprModel}"}"
  match ← run false, ← run true with
  | .ok a, .ok b =>
    let fa := a.toList.map render
    let fb := b.toList.map render
    let withModel := (a.filter (!·.lexprModel.isEmpty)).size
    if fa == fb then
      IO.println s!"{name}: agree on {a.size}{if withModel == 0 then ""
        else s!", {withModel} with a counterexample"}"
    else IO.println s!"{name} differs:\n  per-obligation: {fa}\n  incremental: {fb}"
  | .error a, .error b =>
    IO.println s!"{name}: {if a == b then "both fail alike" else "fail differently"}"
  | _, _ => IO.println s!"{name}: only one fails"

/--
info: DoubleTwice.core.st: agree on 2
HeapReasoning.core.st: agree on 50
IrrelevantAxioms.core.st: agree on 1
LoopSimple.core.st: agree on 8
SafeBvOps.core.st: agree on 8
SimpleProc.core.st: agree on 2
TwoLoops.core.st: agree on 4
-/
#guard_msgs in
#eval show IO Unit from do
  for (path, text) in embeddedExampleFiles do
    if ["DoubleTwice.core.st", "HeapReasoning.core.st", "IrrelevantAxioms.core.st",
        "LoopSimple.core.st", "SafeBvOps.core.st", "SimpleProc.core.st",
        "TwoLoops.core.st"].contains path then
      bothWays path (← parseText text) VerifyOptions.quiet

/-! The same examples with every goal walked, the sessions of one goal included, so the walk is
compared with the per-obligation path rather than that path with itself. -/

/--
info: DoubleTwice.core.st: agree on 2
HeapReasoning.core.st: agree on 50
IrrelevantAxioms.core.st: agree on 1
LoopSimple.core.st: agree on 8
SafeBvOps.core.st: agree on 8
SimpleProc.core.st: agree on 2
TwoLoops.core.st: agree on 4
-/
#guard_msgs in
#eval show IO Unit from do
  for (path, text) in embeddedExampleFiles do
    if ["DoubleTwice.core.st", "HeapReasoning.core.st", "IrrelevantAxioms.core.st",
        "LoopSimple.core.st", "SafeBvOps.core.st", "SimpleProc.core.st",
        "TwoLoops.core.st"].contains path then
      bothWays path (← parseText text) VerifyOptions.quiet (walkAll := true)

/--
info: refutable: agree on 1
refutable: agree on 1
withCover: agree on 2, 2 with a counterexample
withCover: agree on 2, 2 with a counterexample
afterBranch: agree on 3, 3 with a counterexample
afterBranch: agree on 3, 3 with a counterexample
refutable: agree on 1, 1 with a counterexample
refutable: agree on 1, 1 with a counterexample
withCover: agree on 2, 2 with a counterexample
withCover: agree on 2, 2 with a counterexample
afterBranch: agree on 3, 3 with a counterexample
afterBranch: agree on 3, 3 with a counterexample
-/
#guard_msgs in
#eval show IO Unit from do
  for mode in [VerificationMode.bugFinding, VerificationMode.bugFindingAssumingCompleteSpec] do
    for (name, p) in [("refutable", refutable), ("withCover", withCover),
                      ("afterBranch", afterBranch)] do
      for walkAll in [false, true] do
        bothWays name (parse p) { VerifyOptions.quiet with checkMode := mode } (walkAll := walkAll)

/-! `deductiveAssumingSatisfiablePaths` reaches `evaluatorResults` through the incremental back
end too, so the two back ends must agree under it as well. `foldedFalse` holds the goals the
mode's premise decides (`folded`), ones it leaves to the solver (`dead`, under a literally false
assumption, and the cover `never`), and one only a solver can decide (`solver`). -/

private def foldedFalse :=
#strata
program Core;

procedure P()
{
  var x : int;
  assume [pos]: int.gt(x, 0);
  assert [folded]: false;
  if * {
    assume [contra]: false;
    assert [dead]: false;
  }
  cover [never]: false;
  assert [solver]: int.lt(x, 0);
};
#end

/--
info: refutable: agree on 1, 1 with a counterexample
refutable: agree on 1, 1 with a counterexample
withCover: agree on 2, 1 with a counterexample
withCover: agree on 2, 1 with a counterexample
afterBranch: agree on 3, 1 with a counterexample
afterBranch: agree on 3, 1 with a counterexample


Obligation folded: failed!

Result obtained during evaluation.
foldedFalse: agree on 4, 1 with a counterexample


Obligation folded: failed!

Result obtained during evaluation.
foldedFalse: agree on 4, 1 with a counterexample
-/
#guard_msgs in
#eval show IO Unit from do
  for (name, p) in [("refutable", refutable), ("withCover", withCover),
                    ("afterBranch", afterBranch), ("foldedFalse", foldedFalse)] do
    for walkAll in [false, true] do
      bothWays name (parse p)
        { VerifyOptions.quiet with checkMode := .deductiveAssumingSatisfiablePaths }
        (walkAll := walkAll)

/-! A solver option the solver rejects gives every goal the verdict it gets without
`--incremental`: cvc5 has no `timeout` option, and z3 none spelled `tlimit-per` or `:timeout`.
A solver that cannot be started does the same. The two modes word the solver's message
differently, so each goal's verdict is compared up to its first `!`, and the trace the
per-goal discharge prints for a failed solver is kept out of the output.

One setting differs on purpose. z3 answers `tlimit-per` with an error that lists its legal
parameters, `timeout` among them, and the path that writes the query to a file reads any
`timeout` in a solver's output as a timeout. `--incremental` reads the error itself, so it
reports the rejected option as the crash it is. -/

/--
info: cvc5 timeout=500: wrong 🚨 SMT Solver Crash, lo1 🚨 SMT Solver Crash, hi1 🚨 SMT Solver Crash, common 🚨 SMT Solver Crash, fair 🚨 SMT Solver Crash, excl 🚨 SMT Solver Crash
z3 tlimit-per=500 differs:
  per-obligation: #[wrong 🚨 Solver Timeout, lo1 🚨 Solver Timeout, hi1 🚨 Solver Timeout, common 🚨 Solver Timeout, fair 🚨 Solver Timeout, excl 🚨 Solver Timeout]
  incremental: #[wrong 🚨 SMT Solver Crash, lo1 🚨 SMT Solver Crash, hi1 🚨 SMT Solver Crash, common 🚨 SMT Solver Crash, fair 🚨 SMT Solver Crash, excl 🚨 SMT Solver Crash]
z3 :timeout=500: wrong 🚨 SMT Solver Crash, lo1 🚨 SMT Solver Crash, hi1 🚨 SMT Solver Crash, common 🚨 SMT Solver Crash, fair 🚨 SMT Solver Crash, excl 🚨 SMT Solver Crash
nosuch: wrong 🚨 SMT Solver Crash, lo1 🚨 SMT Solver Crash, hi1 🚨 SMT Solver Crash, common 🚨 SMT Solver Crash, fair 🚨 SMT Solver Crash, excl 🚨 SMT Solver Crash
-/
#guard_msgs in
#eval show IO Unit from do
  for (solver, opts) in [("cvc5", #[("timeout", "500")]), ("z3", #[("tlimit-per", "500")]),
                         ("z3", #[(":timeout", "500")]), ("nosuch", #[])] do
    let mut seen : Array (Array String) := #[]
    for incremental in [false, true] do
      let mut verdicts : Array String := #[]
      for p in [refutable, afterBranch, twoGoals] do
        let (_, r) ← IO.FS.withIsolatedStreams (isolateStderr := true)
          (Strata.Core.verifyProgram (parse p)
            { VerifyOptions.quiet with solver, solverOptions := opts, incremental }).toBaseIO
        match r with
        | .ok rs => verdicts := verdicts ++ rs.map fun r =>
            s!"{r.obligation.label} {((r.formatOutcome.splitOn "!").headD "")}"
        | .error e => verdicts := verdicts.push s!"error: {e}"
      seen := seen.push verdicts
    let setting := ", ".intercalate (opts.toList.map fun (k, v) => s!"{k}={v}")
    let head := if setting.isEmpty then solver else s!"{solver} {setting}"
    if seen[0]! == seen[1]! then IO.println s!"{head}: {", ".intercalate seen[0]!.toList}"
    else IO.println s!"{head} differs:\n  per-obligation: {seen[0]!}\n  incremental: {seen[1]!}"

/-! Through a pipeline that runs `simplify` in place of symbolic evaluation, the procedures keep
their parameters, and both modes refute the goals on a parameter named like a constant. -/

private def withoutSymbolicEval : Option (Core.ValidatedPipeline Core.ProgramFactSet.empty) := do
  let ho ← Core.assertPhaseFor (Core.assertPhaseName .hasObligationForm)
  let pc ← Core.assertPhaseFor (Core.assertPhaseName .noProcedureContracts)
  let entry ← [.noCFGBodies, .noCalls, .noLoops, .staticSingleAssignment, .noNondetGuards].mapM
    (fun f => Core.assertPhaseFor (Core.assertPhaseName f))
  (Core.validatePipeline
    (entry ++ [Core.passTermCheck, Core.passPrecondElim, Core.passGenOpaqueTypeParams,
      Core.passTypeCheck .quiet, Core.passMonomorphizeFunctions, Core.passSimplify,
      ho, pc, Core.passFunctionInlining, Core.passBetaReduce])).toOption

/--
info: g ❌ fail, g2 ❌ fail
g ❌ fail, g2 ❌ fail
-/
#guard_msgs in
#eval show IO Unit from do
  for incremental in [false, true] do
    match ← (Strata.Core.verifyProgram (parse paramNamedLikeFunction)
        { VerifyOptions.quiet with incremental } (pipeline := withoutSymbolicEval)).toBaseIO with
    | .ok rs => IO.println (", ".intercalate (rs.toList.map fun r =>
        s!"{r.obligation.label} {r.formatOutcome}"))
    | .error e => IO.println s!"error: {e}"

/-! The same pipeline leaves a node every assertion it had, so through it the programs below put
several goals on one session, and the walk is compared with the per-obligation path on them. -/

/--
info: chainOfThree: agree on 3
twoGoals: agree on 2
refutable: agree on 1, 1 with a counterexample
-/
#guard_msgs in
#eval show IO Unit from do
  for (name, p) in [("chainOfThree", chainOfThree), ("twoGoals", twoGoals),
                    ("refutable", refutable)] do
    bothWays name (parse p) VerifyOptions.quiet (pipeline := withoutSymbolicEval)

/-! ### The pruning mode can change a verdict

`contra` contradicts itself, and `usesF`'s pruning keeps it while `other`'s drops it. Without
`--incremental` each goal is asked its own question: `usesF` holds, `other` fails. Lazy pruning
leaves `contra` on the solver for `other`, which is then proved. Exact pruning, set the way
`--incremental-pruning exact` sets it, gives the per-obligation verdicts. -/

private def contraAxiom :=
#strata
program Core;
function f(x : int) : int;
axiom [contra]: f(0) == 1 && f(0) == 2;
procedure P (x : int) { assert [usesF]: f(0) == 1; assert [other]: x == 3; };
#end

/--
info: per-obligation: usesF ✅ pass, other ❌ fail
lazy: usesF ✅ pass, other ✅ pass
exact: usesF ✅ pass, other ❌ fail
-/
#guard_msgs in
#eval show IO Unit from do
  let base := { VerifyOptions.quiet with removeIrrelevantAxioms := .Aggressive }
  for (name, options) in [("per-obligation", base), ("lazy", { base with incremental := true }),
      ("exact", { base with incremental := true, exactPruning := true })] do
    match ← (Strata.Core.verifyProgram (parse contraAxiom) options
        (pipeline := withoutSymbolicEval)).toBaseIO with
    | .ok rs => IO.println s!"{name}: {", ".intercalate (rs.toList.map fun r =>
        s!"{r.obligation.label} {r.formatOutcome}")}"
    | .error e => IO.println s!"{name}: error: {e}"

/-! A literal SMT-LIB cannot spell, which common-subexpression elimination hoists above the
goals of an unrelated procedure, fails only the goal that uses it: the two goals of the
other procedure leave the definition out and are proved, as on the per-obligation path. -/

private def cseHoistedLiteral :=
#strata
program Core;
function f (s : string) : int;
procedure Unsupported()
{
  assume [h1]: f("a󠀁b") == 1;
  assume [h2]: f("a󠀁b") == 1;
  assert [cse_unsupported]: false;
};
procedure Unrelated()
{
  assume [safe]: f("safe") == 2;
  assert [cse_unrelated]: f("safe") == 2;
  assert [cse_unrelated_too]: int.ge(f("safe"), 2);
};
#end

/-- info: cseHoistedLiteral: agree on 3 -/
#guard_msgs in
#eval bothWays "cseHoistedLiteral" (parse cseHoistedLiteral) VerifyOptions.quiet

/-! With every goal walked, `cse_unrelated` and `cse_unrelated_too` are checked on a solver that
walks the node the literal was hoisted to, so they agree with the per-obligation path only if they
leave the definition holding it out. -/

/-- info: cseHoistedLiteral walked: agree on 3 -/
#guard_msgs in
#eval bothWays "cseHoistedLiteral walked" (parse cseHoistedLiteral) VerifyOptions.quiet
  (walkAll := true)

/-! ### A counterexample reports the declared variables and no defined or generated name

Whether a variable gets a value in a counterexample depends on whether its value is free, not on
how it is encoded. Through the pipeline without symbolic evaluation, `var x` stays a declaration
of the passive program, and the counterexample to `x >= 11` still gives `x` a value, without
`--incremental`, with it, and with every goal walked, while a variable defined from `x` is left
out. Through the default pipeline, common-subexpression elimination hoists `f(x + 1)` into a
variable of its own, which the counterexample leaves out, while it reports `x`. -/

/-- The names each goal's counterexample reports, without `--incremental`, with it,
    and with every goal walked, and the generated names its path declares. -/
private def modelNames (p : Core.Program)
    (pipeline : Option (Core.ValidatedPipeline Core.ProgramFactSet.empty) := none) :
    IO Unit := do
  for (mode, incremental, walkAll) in
      [("per-obligation", false, false), ("incremental", true, false), ("walked", true, true)] do
    let options := { VerifyOptions.quiet with incremental }
    let solver := if walkAll then
        some (Core.IncrementalSolve.coreSMTSolver options.parallelWorkers options
          (axiomProgram := some p) (sendAlone := false))
      else none
    match ← (Strata.Core.verifyProgram p options (pipeline := pipeline)
        (solver := solver)).toBaseIO with
    | .ok rs =>
      for r in rs do
        let generated := r.obligation.assumptions.flatten.filterMap fun
          | .varDecl name _ _ => if _root_.Core.CSE.isCSEGeneratedName name.name then some name.name
            else none
          | _ => none
        IO.println s!"{mode} {r.obligation.label}: {r.lexprModel.map (·.1.name)}\
          {if generated.isEmpty then "" else s!", generated {generated}"}"
    | .error e => IO.println s!"{mode}: error {e}"

private def declaredVar :=
#strata
program Core;
procedure P()
{
  var x : int;
  assume [pos]: int.gt(x, 0);
  assert [big]: int.ge(x, 11);
};
#end

/--
info: per-obligation big: [x]
incremental big: [x]
walked big: [x]
-/
#guard_msgs in
#eval modelNames (parse declaredVar) (pipeline := withoutSymbolicEval)

/-- A variable the passive program defines is left out, since its value follows from the ones
    reported: `y := x + 1` reports `x` alone. -/
private def definedVar :=
#strata
program Core;
procedure P()
{
  var x : int;
  assume [pos]: int.gt(x, 0);
  var y : int := int.add(x, 1);
  assert [big]: int.ge(y, 11);
};
#end

/--
info: per-obligation big: [x]
incremental big: [x]
walked big: [x]
-/
#guard_msgs in
#eval modelNames (parse definedVar) (pipeline := withoutSymbolicEval)

/-- A chain of fifty definitions reaches `x` from the goal, and reports `x` alone: the closure
    over definitions follows the whole chain, and leaves every defined link out. -/
private def definitionChain :=
#strata
program Core;
procedure P()
{
  var x : int;
  assume [pos]: int.gt(x, 0);
  var x1 : int := int.add(x, 1);
  var x2 : int := int.add(x1, 1);
  var x3 : int := int.add(x2, 1);
  var x4 : int := int.add(x3, 1);
  var x5 : int := int.add(x4, 1);
  var x6 : int := int.add(x5, 1);
  var x7 : int := int.add(x6, 1);
  var x8 : int := int.add(x7, 1);
  var x9 : int := int.add(x8, 1);
  var x10 : int := int.add(x9, 1);
  var x11 : int := int.add(x10, 1);
  var x12 : int := int.add(x11, 1);
  var x13 : int := int.add(x12, 1);
  var x14 : int := int.add(x13, 1);
  var x15 : int := int.add(x14, 1);
  var x16 : int := int.add(x15, 1);
  var x17 : int := int.add(x16, 1);
  var x18 : int := int.add(x17, 1);
  var x19 : int := int.add(x18, 1);
  var x20 : int := int.add(x19, 1);
  var x21 : int := int.add(x20, 1);
  var x22 : int := int.add(x21, 1);
  var x23 : int := int.add(x22, 1);
  var x24 : int := int.add(x23, 1);
  var x25 : int := int.add(x24, 1);
  var x26 : int := int.add(x25, 1);
  var x27 : int := int.add(x26, 1);
  var x28 : int := int.add(x27, 1);
  var x29 : int := int.add(x28, 1);
  var x30 : int := int.add(x29, 1);
  var x31 : int := int.add(x30, 1);
  var x32 : int := int.add(x31, 1);
  var x33 : int := int.add(x32, 1);
  var x34 : int := int.add(x33, 1);
  var x35 : int := int.add(x34, 1);
  var x36 : int := int.add(x35, 1);
  var x37 : int := int.add(x36, 1);
  var x38 : int := int.add(x37, 1);
  var x39 : int := int.add(x38, 1);
  var x40 : int := int.add(x39, 1);
  var x41 : int := int.add(x40, 1);
  var x42 : int := int.add(x41, 1);
  var x43 : int := int.add(x42, 1);
  var x44 : int := int.add(x43, 1);
  var x45 : int := int.add(x44, 1);
  var x46 : int := int.add(x45, 1);
  var x47 : int := int.add(x46, 1);
  var x48 : int := int.add(x47, 1);
  var x49 : int := int.add(x48, 1);
  var x50 : int := int.add(x49, 1);
  assert [big]: int.gt(x50, 1000);
};
#end

/--
info: per-obligation big: [x]
incremental big: [x]
walked big: [x]
-/
#guard_msgs in
#eval modelNames (parse definitionChain) (pipeline := withoutSymbolicEval)

private def hoistedTerm :=
#strata
program Core;
function f (x : int) : int;
procedure P()
{
  var x : int;
  assume [pos]: int.gt(f(int.add(x, 1)), 0);
  assume [small]: int.lt(f(int.add(x, 1)), 5);
  assert [big]: int.gt(f(int.add(x, 1)), 10);
};
#end

/--
info: per-obligation big: [x], generated [$__cse.0]
incremental big: [x], generated [$__cse.0]
walked big: [x], generated [$__cse.0]
-/
#guard_msgs in
#eval modelNames (parse hoistedTerm)

/-! ### A goal the solver cannot be told fails alone, inside the walk

`bad` and `good` sit on one node of one session, so the walk itself meets the literal SMT-LIB
cannot spell, not the per-obligation discharge a session of one would go to. `bad` reports the
encoding error, and `good`, checked after it on the same session, is still proved. -/

private def badNextToGood :=
#strata
program Core;
function f (s : string) : int;
procedure P()
{
  var x : int;
  assume [pos]: int.gt(x, 0);
  assert [bad]: f("a󠀁b") == x;
  assert [good]: int.ge(x, 1);
};
#end

/--
info: bad: error
good: proved
-/
#guard_msgs in
#eval show IO Unit from do
  match ← Core.IncrementalSolve.verifyProgram (parse badNextToGood) 1 with
  | .ok (results, _, _) =>
    for r in results do IO.println s!"{r.obligation.label}: {Core.IncrementalSolve.verdictOf r}"
  | .error e => IO.println s!"error: {e}"

/-! A recursive function sent as `define-fun-rec`, which leaves out the per-constructor axioms,
and a subset of the obligations asked for by label: each gives the per-obligation results. -/

private def recursiveLength :=
#strata
program Core;
datatype IntList { Nil(), Cons(hd: int, tl: IntList) };
rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else int.add(1, listLen(IntList..tl(xs)))
};
procedure P(xs : IntList)
spec {
  requires IntList..isCons(xs);
}
{
  assert [len_step]: listLen(xs) == int.add(1, listLen(IntList..tl(xs)));
};
#end

/-- info: recursiveLength: agree on 4 -/
#guard_msgs in
#eval bothWays "recursiveLength" (parse recursiveLength)
  { VerifyOptions.quiet with recursiveFnsAsDefineFunRec := true }

/-- info: twoGoals subset: agree on 1 -/
#guard_msgs in
#eval bothWays "twoGoals subset" (parse twoGoals)
  { VerifyOptions.quiet with obligationsToVerify := some ["fair"] }

/-! A counterexample that holds a datatype value, walked: its constructors come back as
constructors, as on the per-obligation path, and not as free variables of the same name. -/

private def datatypeCounterexample :=
#strata
program Core;
datatype IntList { Nil(), Cons(hd: int, tl: IntList) };
procedure P(xs : IntList)
spec {
  requires IntList..isCons(xs);
}
{
  assert [short]: IntList..isNil(IntList..tl(xs));
  assert [positive]: int.gt(IntList..hd(xs), 0);
};
#end

/-- The constructors and variables a counterexample value is built from, each with what it was
    read as, since a constructor and a variable of the same name print alike. -/
private def headsOf : Lambda.LExpr Core.CoreLParams.mono → List String
  | .op _ o _ => [s!"constructor {o.name}"]
  | .fvar _ v _ => [s!"variable {v.name}"]
  | .app _ f a => headsOf f ++ headsOf a
  | _ => []

/--
info: per-obligation: [constructor Cons, constructor Nil]
walked: [constructor Cons, constructor Nil]
-/
#guard_msgs in
#eval show IO Unit from do
  let p := parse datatypeCounterexample
  let options := { VerifyOptions.quiet with checkMode := .bugFinding }
  for (name, incremental) in [("per-obligation", false), ("walked", true)] do
    let options := { options with incremental }
    let solver := if incremental then
        some (Core.IncrementalSolve.coreSMTSolver 1 options (axiomProgram := some p)
          (sendAlone := false))
      else none
    match ← (Strata.Core.verifyProgram p options (solver := solver)).toBaseIO with
    | .ok rs =>
      let heads := rs.toList.flatMap fun r => r.lexprModel.flatMap (headsOf ·.2)
      IO.println s!"{name}: {heads.eraseDups}"
    | .error e => IO.println s!"{name}: error {e}"

/-! Symbolic evaluation leaves two copies of `A`, one per path to it, with the same label and
the same metadata. Each is a session of one goal and is sent alone, and each keeps its own
answer: `A` fails on one path and holds on the other, in both modes. -/

private def twoPathsOneLabel :=
#strata
program Core;
procedure P(x : int, out y : int)
{
  l1: {
    l2: {
      if (int.gt(x, 0)) { y := int.sub(0, x); exit l2; } else { y := int.sub(1, x); exit l1; }
    }
    assert [B]: int.lt(y, 0);
  }
  assert [A]: int.gt(y, 0);
};
#end

/-- info: twoPathsOneLabel: agree on 2, 1 with a counterexample -/
#guard_msgs in
#eval bothWays "twoPathsOneLabel" (parse twoPathsOneLabel) VerifyOptions.quiet

/-- info: twoPathsOneLabel with 4 sessions: agree on 2, 1 with a counterexample -/
#guard_msgs in
#eval bothWays "twoPathsOneLabel with 4 sessions" (parse twoPathsOneLabel)
  { VerifyOptions.quiet with minSessions := some 4 }

/-! Under `--stop-on-first-error`, every goal of this procedure is a session of one goal once
symbolic evaluation has run, so all of them are sent to the per-obligation discharge, which stops
at `f1bad`. The goals it never reached are left out in both modes. -/

private def stopsMidway :=
#strata
program Core;
procedure P()
{
  var x : int;
  assume [pos]: int.gt(x, 0);
  assert [f1]: int.ge(x, 1);
  assert [f1bad]: int.lt(x, 0);
  assert [gx]: int.ge(x, 0);
  assert [xs]: int.gt(int.add(x, 5), 0);
};
#end

/-- info: stopsMidway: agree on 2, 1 with a counterexample -/
#guard_msgs in
#eval bothWays "stopsMidway" (parse stopsMidway)
  { VerifyOptions.quiet with stopOnFirstError := true }

/-! ### A run that can start no solver sends every goal alone

A factory whose sessions are always refused leaves the walk without a solver, and every goal is
sent the per-obligation way, the two that share a procedure included. A factory that refuses only
its first session leaves the walk with the next one, which the patient start waits for. -/

private def refusingFactory (refuse : Nat → Bool) (spawns : IO.Ref Nat) :
    Core.IncrementalSolve.SessionFactory :=
  { τ := Strata.SMT.Term, σ := Strata.SMT.TermType
    spawn := fun options => do
      let n ← spawns.modifyGet fun n => (n, n + 1)
      if refuse n then throw (IO.userError "session refused")
      localCvc5 options }

/--
info: always refused: b1 proved, b2 proved, s1 proved, a1 proved, a2 proved; sessions asked for: 3
first refused: b1 proved, b2 proved, s1 proved, a1 proved, a2 proved; sessions asked for: 2
-/
#guard_msgs in
#eval show IO Unit from do
  for (name, refuse) in [("always refused", fun (_ : Nat) => true),
                         ("first refused", fun (n : Nat) => n == 0)] do
    let spawns ← IO.mkRef 0
    let solver : Core.CoreSMTSolver := Core.IncrementalSolve.coreSMTSolver 1
      (session := some (refusingFactory refuse spawns))
    let (_, r) ← IO.FS.withIsolatedStreams (isolateStderr := true)
      (solver Core.Factory (parse oneGoalBetweenTwo)).toIO'
    match r with
    | .ok (results, _) =>
      let verdicts := results.toList.map fun r => s!"{r.obligation.label} {verdictOf r}"
      IO.println s!"{name}: {", ".intercalate verdicts}; sessions asked for: {← spawns.get}"
    | .error e => IO.println s!"{name}: error: {e.format none}"

/-! ### The solver's own bookkeeping

`(reset)` empties the solver, so the count `declareNew` renames a shadowed name by goes with it:
`x` declared again after a reset is `x` again, and a definition over it is accepted. A name
declared while a quantifier's body is encoded is remembered once the quantifier is built, so the
next declaration of it is renamed. -/

private def onCvc5 (act : Strata.SMT.AbstractSolver Strata.SMT.Term Strata.SMT.TermType
    Strata.SMT.IncrementalEncodingM → Strata.SMT.IncrementalEncodingM String) : IO Unit := do
  let st ← Strata.SMT.IncrementalSolver.spawn "cvc5" #["--quiet", "--lang", "smt", "--incremental"]
  let s := Strata.SMT.IncrementalSolver.mkIncrementalSolver st
  try
    match ← (do s.setLogic "ALL"; act s).run with
    | .ok out => IO.println out
    | .error e => IO.println s!"encoding error: {repr e}"
  catch e => IO.println s!"error: {e}"
  finally try discard s.close.run catch _ => pure ()

private def nameOf : Strata.SMT.Term → String
  | .var v => v.id
  | _ => "?"

/-- info: before reset: x, after reset: x, definition accepted: sat -/
#guard_msgs in
#eval onCvc5 fun s => do
  let x1 ← s.declareNew "x" .int
  s.reset
  s.setLogic "ALL"
  let x2 ← s.declareNew "x" .int
  s.defineFun "d" [] .int x2
  let d ← s.checkSat
  let verdict := match d with | .sat => "sat" | .unsat => "unsat" | _ => "other"
  return s!"before reset: {nameOf x1}, after reset: {nameOf x2}, definition accepted: {verdict}"

/-- info: inside the quantifier: y, after it: y@1 -/
#guard_msgs in
#eval onCvc5 fun s => do
  let inner ← IO.mkRef ""
  let _ ← s.mkForall [("b", .int)] fun _ => do
    let y ← s.declareNew "y" .int
    inner.set (nameOf y)
    return (Strata.SMT.Term.bool true, [])
  let y ← s.declareNew "y" .int
  return s!"inside the quantifier: {← inner.get}, after it: {nameOf y}"

end Core.IncrementalSolve.Tests
end
