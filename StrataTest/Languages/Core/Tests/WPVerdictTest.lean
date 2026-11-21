/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier
import Strata.Languages.Core
import Strata.MetaVerifier
import StrataTest.Languages.Core.Tests.WPTestUtils

/-! # Verdicts of `--vcgen wp` on branches that are never taken

Under `--vcgen wp` the obligations of a branch whose condition is `false` are reported, on a path
assuming `false`, as symbolic evaluation reports them; the code after an `exit` is not run, and
its obligations are not reported, in both modes; a variable assigned before an exit keeps, at
the exit's target, the value it had at the exit; a postcondition on variables assigned
literals, an assertion after an exit on a variable assigned a literal, and an assertion on a
user-defined function with a concrete evaluator applied to a literal are closed without a solver
in both modes; an assertion on the application of a local function fails in both modes; and the
obligations of nested local functions that apply the previous one twice, and of applications of a
local function nested in one expression, stay small. -/

namespace Strata.WPVerdictTest

open Strata.WPTestUtils

/-- A branch whose condition is `false` (from `Examples/Cover.lean`). -/
def falseBranchPgm :=
#strata
program Core;
procedure Test()
{
  var x : int;
  assume (int.ge(x, 0));

  if (false) {
    cover [unreachable_cover1]: (true);
    cover [unreachable_cover2]: (false);
    assert [unreachable_assert]: (false);
  } else {
    cover [reachable_cover]: (true);
    cover [unsatisfiable_cover]: (x == int.neg(1));
    assert [reachable_assert]: (true);
  }
};
#end

/-- Exits (from `Examples/Exit.lean`). -/
def exitPgm :=
#strata
program Core;
procedure Test1(x : bool, out y : bool)
{
    l1: {
      assert [a1]: x == x;
      exit l1;
      assert [a2]: !(x == x); // skipped because we exited l1
    }
    assert [a3]: x == x;
};

procedure Test2(x : int, out y : bool)
{
    l5: {
      l4: {
        l4_before: {
          l3_before: {
            l1: {
              assert [a4]: x == x;
              if (int.gt(x, 0)) {
                exit l3_before;
              } else {
                exit l4_before;
              }
            }
            l2: {
              assert [a5]: !(x == x); // skipped over
            }
          }
          assert [a6]: int.gt(int.mul(x, 2), x);
          exit l5;
        }
        assert [a7]: int.le(x, 0);
        exit l5;
      }
    }
};
#end

/-- An exit, then an `ite` whose two arms exit to the same block and assign the same variable. -/
def earlyExitPgm :=
#strata
program Core;
procedure P(out x : int, out y : int)
{
  assume [h]: int.ge(x, y);
  Out: {
    L3: {
      if (int.add(x, 0) == 1) {} else { x := int.add(y, int.neg(4)); exit Out; }
    }
    if (int.gt(6, 0)) { x := int.add(y, 2); exit Out; } else { x := int.add(y, 1); exit Out; }
  }
  assert [early]: int.ge(x, y);
};

procedure Min1(c : int, d : int, out x : int, out y : int)
{
  Out: {
    L0: {
      if (int.ge(int.add(d, 4), 2)) {} else { x := y; exit Out; }
      y := x;
    }
    if (d == 1) { x := y; exit Out; } else { x := int.add(x, 4); exit Out; }
  }
  assert [min1]: int.ge(x, y);
};

procedure Min2(c : int, d : int, out x : int, out y : int)
{
  Out: {
    L3: {
      if (int.add(x, 0) == 1) {} else { x := int.add(y, 4); exit Out; }
    }
    if (int.gt(6, 0)) { x := int.add(y, 2); exit Out; } else { x := int.add(x, y); exit Out; }
  }
  assert [min2]: int.ge(x, y);
};

procedure Min3(c : int, d : int, out x : int, out y : int)
{
  L0: {
    L1: {
      L2: {
        L3: {
          if (int.gt(int.add(d, 3), 0)) {} else { x := int.add(c, d); exit L0; }
          assume [h6]: 3 == 1;
        }
      }
    }
    if (4 == 1) { x := c; exit L0; } else { havoc x; exit L0; }
  }
  if (int.gt(x, 0)) {
    L36: {
      assert [a37]: int.gt(c, 0);
    }
  } else {}
};
#end

/-- Variants: two earlier exits; an exit two blocks deep; an earlier `ite` whose two arms
    exit; different variables in the arms. -/
def earlyExitVariantsPgm :=
#strata
program Core;
procedure TwoExits(out x : int, out y : int)
{
  assume [h]: int.ge(x, y);
  Out: {
    L1: { if (x == 1) {} else { x := int.add(y, int.neg(4)); exit Out; } }
    L2: { if (x == 2) {} else { x := int.add(y, int.neg(5)); exit Out; } }
    if (int.gt(6, 0)) { x := int.add(y, 2); exit Out; } else { x := int.add(y, 1); exit Out; }
  }
  assert [two]: int.ge(x, y);
};

procedure Deep(out x : int, out y : int)
{
  assume [h]: int.ge(x, y);
  Out: {
    L1: { L2: { if (x == 1) {} else { x := int.add(y, int.neg(4)); exit Out; } } }
    if (int.gt(6, 0)) { x := int.add(y, 2); exit Out; } else { x := int.add(y, 1); exit Out; }
  }
  assert [deep]: int.ge(x, y);
};

procedure BothEarly(c : int, d : int, out x : int, out y : int)
{
  assume [h]: int.ge(x, y);
  Out: {
    L1: {
      if (int.gt(c, 0)) {
        if (x == 1) { x := int.add(y, int.neg(4)); exit Out; }
        else { x := int.add(y, int.neg(5)); exit Out; }
      } else {}
    }
    if (int.gt(d, 0)) { x := int.add(y, 2); exit Out; } else { x := int.add(y, 1); exit Out; }
  }
  assert [both]: int.ge(x, y);
};

procedure Vars(d : int, out x : int, out y : int)
{
  assume [h]: int.ge(x, y);
  Out: {
    L1: {
      if (x == 1) {} else { y := int.add(y, int.neg(1)); x := int.add(y, int.neg(4)); exit Out; }
    }
    if (int.gt(d, 0)) { y := int.add(y, int.neg(1)); x := int.add(y, 2); exit Out; }
    else { x := int.add(y, 1); exit Out; }
  }
  assert [vars]: int.ge(x, y);
};
#end

/--
info: symbolic: unreachable_cover1 uncovered, unreachable_cover2 uncovered, unreachable_assert proved, reachable_cover covered, unsatisfiable_cover uncovered, reachable_assert proved
wp: unreachable_cover1 uncovered, unreachable_cover2 uncovered, unreachable_assert proved, reachable_cover covered, unsatisfiable_cover uncovered, reachable_assert proved
-/
#guard_msgs in
#eval printModesVerdicts falseBranchPgm

/--
info: symbolic: a1 proved, a3 proved, a4 proved, a6 proved, a7 proved
wp: a1 proved, a3 proved, a4 proved, a6 proved, a7 proved
-/
#guard_msgs in
#eval printModesVerdicts exitPgm

/--
info: symbolic: a37 proved, early refuted, min1 proved, min2 proved
wp: a37 proved, early refuted, min1 proved, min2 proved
-/
#guard_msgs in
#eval printModesVerdicts earlyExitPgm (sorted := true)

/--
info: symbolic: both refuted, deep refuted, two refuted, vars refuted
wp: both refuted, deep refuted, two refuted, vars refuted
-/
#guard_msgs in
#eval printModesVerdicts earlyExitVariantsPgm (sorted := true)

/-! ## The labels of `verdict`

One result of each kind that `verdict` names, and one it does not claim: a validity check that
is `unsat` is `proved`; one that is `sat` is `refuted`; `unknown` to both checks is `unknown`;
an encoding error, a solver crash and a timeout are `error`; a solver error on a check, which
none of these claims, is `other`, and so is an unsatisfiable assertion whose validity check gave
up, which has no counterexample. A cover is `covered` when satisfiable and `uncovered` when
unsatisfiable. -/

/-- The result of an obligation of kind `prop`, an assertion by default, with the outcome `o`. -/
private def resultOf (o : Except Core.VCError Core.VCOutcome)
    (prop : Imperative.PropertyType := .assert) : Core.VCResult :=
  { obligation := { label := "a", property := prop, assumptions := [],
                    obligation := .boolConst Core.valueLoc true, metadata := {} },
    outcome := o }

#guard verdict (resultOf (.ok { satisfiabilityProperty := .unknown, validityProperty := .unsat }))
  == "proved"
#guard verdict (resultOf (.ok { satisfiabilityProperty := .unknown, validityProperty := .sat [] }))
  == "refuted"
#guard verdict (resultOf (.ok { satisfiabilityProperty := .unknown, validityProperty := .unknown }))
  == "unknown"
#guard verdict (resultOf (.error (.encoding ""))) == "error"
#guard verdict (resultOf (.error (.solverCrash ""))) == "error"
#guard verdict (resultOf (.error (.solverTimeout ""))) == "error"
#guard verdict (resultOf (.ok { satisfiabilityProperty := .unknown, validityProperty := .err "" }))
  == "other"
#guard verdict (resultOf (.ok { satisfiabilityProperty := .unsat, validityProperty := .unknown }))
  == "other"
#guard verdict (resultOf (.ok { satisfiabilityProperty := .sat [], validityProperty := .unknown })
  (prop := .cover)) == "covered"
#guard verdict (resultOf (.ok { satisfiabilityProperty := .unsat, validityProperty := .unknown })
  (prop := .cover)) == "uncovered"

/-- Postconditions on variables assigned literals (from `Logic/Hoare.lean`). -/
def litPostPgm :=
#strata
program Core;
procedure Set1(out y : int)
spec {
  ensures [set1]: y == 1;
}
{
  y := 1;
};
procedure InitVar(out y : int)
spec {
  ensures [initVar]: y == 3;
}
{
  var t : int := 3;
  y := t;
};
#end

-- No solver is available (`solver` names no executable), so an obligation is proved only when
-- the pipeline closes it without a solver: under `--vcgen wp` the SSA phase records the literal
-- values and evaluates each postcondition to `true`.
/--
info: symbolic set1: proved
symbolic initVar: proved
wp set1: proved
wp initVar: proved
-/
#guard_msgs in
#eval show IO Unit from do
  for (mode, opts) in modes do
    let opts' : Core.VerifyOptions := { opts with solver := "not-a-local-solver" }
    printProved litPostPgm opts' (pre := s!"{mode} ")

/-- An assignment after an exit is not run: at the exit's target `x` is `1`. -/
def deadAfterExitPgm :=
#strata
program Core;
procedure DeadAfterExit()
{
  var x : int;
  L: {
    x := 1;
    exit L;
    x := int.add(x, 1);
    assert [p]: int.gt(x, 0);
  }
  assert [q]: int.gt(x, 0);
};
#end

-- No solver is available: under `--vcgen wp` the SSA phase records `x := 1` and evaluates
-- `int.gt(1, 0)` by the concrete evaluator of `Int.Gt`.
/--
info: symbolic q: proved
wp q: proved
-/
#guard_msgs in
#eval show IO Unit from do
  for (mode, opts) in modes do
    let opts' : Core.VerifyOptions := { opts with solver := "not-a-local-solver" }
    printProved deadAfterExitPgm opts' (pre := s!"{mode} ")

/-- A user-defined function with a concrete evaluator: `dbl x` is `2 * x`. -/
def dblFunc : Lambda.LFunc Core.CoreLParams :=
  { name := "dbl", typeArgs := [], inputs := [(⟨"x", ()⟩, .int)], output := .int,
    concreteEval := some fun md _ args => match args with
      | [x] => (Lambda.LExpr.denoteInt x).map fun v => .intConst md (2 * v)
      | _ => none }

/-- A procedure asserting `dbl 21 == 42`. -/
def dblProgram : Core.Program :=
  let md : Imperative.MetaData Core.Expression := #[]
  let y : Core.CoreIdent := ⟨"y", ()⟩
  let dbl21 : Core.Expression.Expr :=
    .app Core.valueLoc (.op Core.valueLoc ⟨"dbl", ()⟩ (some (.arrow .int .int))) (.intConst Core.valueLoc 21)
  { decls := [.proc {
      header := { name := ⟨"Dbl", ()⟩, typeArgs := [], inputs := [], outputs := [] },
      spec := { preconditions := [], postconditions := [] },
      body := .structured [.cmd (.cmd (.init y (.forAll [] .int) (.det dbl21) md)),
        .cmd (.cmd (.assert "p" (.eq Core.valueLoc (.fvar Core.valueLoc y (some .int)) (.intConst Core.valueLoc 42)) md))] false }
      .empty] }

-- No solver is available: under `--vcgen wp` the SSA phase evaluates `dbl(21)` by the concrete
-- evaluator `moreFns` supplies.
/--
info: symbolic p: proved
wp p: proved
-/
#guard_msgs in
#eval show IO Unit from do
  for (mode, opts) in modes do
    let opts' : Core.VerifyOptions := { opts with solver := "not-a-local-solver" }
    let rs ← (Core.verifyProgram dblProgram opts' (Lambda.Factory.ofArray #[dblFunc])).toIO
      fun e => IO.userError e
    for r in rs do
      IO.println s!"{mode} {r.obligation.label}: {if r.isSuccess then "proved" else "not proved"}"

/-- A local function that captures a variable (from `Transform/SimplifyTests.lean`). -/
def localFuncPgm :=
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

-- The SSA phase substitutes the function value into its application, which `betaReduce` then
-- reduces: the assertion is refuted in both modes.
/--
info: symbolic: ok refuted
wp: ok refuted
-/
#guard_msgs in
#eval printModesVerdicts localFuncPgm

/-- Testers applied to constructors, one with a field that is a parameter. -/
def testerPgm :=
#strata
program Core;
datatype Opt { None(), Some(val : int) };
procedure Testers(x : int)
{
  var o : Opt := Some(x);
  var n : Opt := None();
  assert [isSome]: Opt..isSome(o);
  assert [notNone]: !(Opt..isNone(o));
  assert [isNone]: Opt..isNone(n);
};
#end

-- No solver is available: under `--vcgen wp` the rewrite loop inlines the definitions and folds
-- each tester applied to a constructor by the tester's body and the eliminator's evaluator.
/--
info: symbolic isSome: proved
symbolic notNone: proved
symbolic isNone: proved
wp isSome: proved
wp notNone: proved
wp isNone: proved
-/
#guard_msgs in
#eval show IO Unit from do
  for (mode, opts) in modes do
    let opts' : Core.VerifyOptions := { opts with solver := "not-a-local-solver" }
    printProved testerPgm opts' (pre := s!"{mode} ")

/-- An assignment in a block left by an `exit` to an enclosing block, followed in that block by
    unreachable code: the variable's declaration is kept with the assignment.  `Base` and
    `InitBase` (declared with a value) have all three ingredients; `NoAssign`, `ExitInner` and
    `NothingAfter` each lack one; in `AfterOuter` the obligation follows the outer block. -/
def exitPastLocalPgm :=
#strata
program Core;
procedure Base()
{
  var w : int;
  L3: {
    L4: {
      w := 0;
      exit L3;
    }
    assert [base]: false;
  }
};

procedure InitBase()
{
  var w : int := 1;
  L3: {
    L4: {
      w := 0;
      exit L3;
    }
    assert [initBase]: false;
  }
};

procedure NoAssign()
{
  var w : int;
  L3: {
    L4: {
      exit L3;
    }
    assert [noAssign]: false;
  }
};

procedure ExitInner()
{
  var w : int;
  L3: {
    L4: {
      w := 0;
      exit L4;
    }
    assert [exitInner]: w == 0;
  }
};

procedure NothingAfter()
{
  var w : int;
  L3: {
    L4: {
      w := 0;
      exit L3;
    }
  }
};

procedure AfterOuter()
{
  var w : int;
  L3: {
    L4: {
      w := 0;
      exit L3;
    }
  }
  assert [afterOuter]: w == 0;
};
#end

/--
info: symbolic: exitInner proved, afterOuter proved
wp: exitInner proved, afterOuter proved
-/
#guard_msgs in
#eval printModesVerdicts exitPastLocalPgm

/-! A counterexample under `--vcgen wp` names the same variables with and without
`--incremental`: those the goal and its sliced path read, so not `z`, which only the
definition of `u`, unread by `a`, reads. -/

def modelVarsPgm :=
#strata
program Core;
procedure P(x : int, z : int)
{
  var u : int := int.add(z, 1);
  assert [a]: int.gt(x, 0);
  assert [b]: int.gt(u, 1);
  assert [c]: int.lt(u, 100);
};
#end

/--
info: incremental=false a: model=[x@0]
incremental=true a: model=[x@0]
-/
#guard_msgs in
#eval do
  for incremental in [false, true] do
    for r in ← Core.verify modelVarsPgm
        (options := { Core.VerifyOptions.quiet with vcgen := .wp, incremental }) do
      if r.obligation.label == "a" then
        let names : List String := r.lexprModel.map fun (p : Core.Expression.Ident × _) =>
          toString (Std.format p.1)
        IO.println s!"incremental={incremental} a: model={names}"

/-! Nested local functions, each applying the previous one twice: beta-reducing the
substituted function values would double the obligation at each level (in `squareChain`, whose
innermost function also reads its argument twice) or build one copy of the innermost body per
application (in `addChain`).  The SSA phase records only small function values no beta
reduction of which copies a function value, so under `--vcgen wp` the obligations stay small:
their printed form has fewer than 1000 characters. -/

/-- Five levels over `v * v + n`. -/
def squareChain :=
#strata
program Core;
procedure F(n : int)
{
  function f0 (v : int) : int { int.add(int.mul(v, v), n) }
  function f1 (v : int) : int { f0(f0(v)) }
  function f2 (v : int) : int { f1(f1(v)) }
  function f3 (v : int) : int { f2(f2(v)) }
  function f4 (v : int) : int { f3(f3(v)) }
  function f5 (v : int) : int { f4(f4(v)) }
  var r : int := f5(n);
  assert [ok]: int.ge(r, int.neg(1000000));
};
#end

/-- Ten levels over `v + n`. -/
def addChain :=
#strata
program Core;
procedure F(n : int)
{
  function f0 (v : int) : int { int.add(v, n) }
  function f1 (v : int) : int { f0(f0(v)) }
  function f2 (v : int) : int { f1(f1(v)) }
  function f3 (v : int) : int { f2(f2(v)) }
  function f4 (v : int) : int { f3(f3(v)) }
  function f5 (v : int) : int { f4(f4(v)) }
  function f6 (v : int) : int { f5(f5(v)) }
  function f7 (v : int) : int { f6(f6(v)) }
  function f8 (v : int) : int { f7(f7(v)) }
  function f9 (v : int) : int { f8(f8(v)) }
  function f10 (v : int) : int { f9(f9(v)) }
  var r : int := f10(n);
  assert [ok]: int.ge(r, int.neg(1000000));
};
#end

/--
info: squareChain: true
addChain: true
-/
#guard_msgs in
#eval show IO Unit from do
  for (name, pgm) in [("squareChain", squareChain), ("addChain", addChain)] do
    let opts := { Core.VerifyOptions.quiet with vcgen := .wp, skipSolver := true }
    for r in ← Core.verify pgm (options := opts) do
      IO.println s!"{name}: {decide ((toString (Std.format r.obligation)).length < 1000)}"

/-! Applications of a local function nested in one expression: beta-reducing the substituted
function value `f0` (`v * v + n`, which reads its argument twice) would double the obligation at
each level.  The SSA phase writes a function value that reads an argument twice only where each
application of its name is to a literal or a variable, so under `--vcgen wp` the obligation reads
`f0` by its name and stays small: its printed form has fewer than 1000 characters at ten and at
eighteen levels, and with twenty levels alternating `f0` with a function that reads its argument
once. -/

/-- Ten nested applications of `v * v + n`. -/
def squareNest10 :=
#strata
program Core;
procedure F(n : int)
{
  function f0 (v : int) : int { int.add(int.mul(v, v), n) }
  var r : int := f0(f0(f0(f0(f0(f0(f0(f0(f0(f0(n))))))))));
  assert [ok]: int.ge(r, int.neg(1000000));
};
#end

/-- Eighteen nested applications of `v * v + n`. -/
def squareNest18 :=
#strata
program Core;
procedure F(n : int)
{
  function f0 (v : int) : int { int.add(int.mul(v, v), n) }
  var r : int := f0(f0(f0(f0(f0(f0(f0(f0(f0(f0(f0(f0(f0(f0(f0(f0(f0(f0(n))))))))))))))))));
  assert [ok]: int.ge(r, int.neg(1000000));
};
#end

/-- Twenty nested applications alternating `v * v + n` and `v + n`. -/
def mixedNest :=
#strata
program Core;
procedure F(n : int)
{
  function g (v : int) : int { int.add(int.mul(v, v), n) }
  function h (v : int) : int { int.add(v, n) }
  var r : int := h(g(h(g(h(g(h(g(h(g(h(g(h(g(h(g(h(g(h(g(n))))))))))))))))))));
  assert [ok]: int.ge(r, int.neg(1000000));
};
#end

/--
info: squareNest10: true
squareNest18: true
mixedNest: true
-/
#guard_msgs in
#eval show IO Unit from do
  for (name, pgm) in [("squareNest10", squareNest10), ("squareNest18", squareNest18),
      ("mixedNest", mixedNest)] do
    let opts := { Core.VerifyOptions.quiet with vcgen := .wp, skipSolver := true }
    for r in ← Core.verify pgm (options := opts) do
      IO.println s!"{name}: {decide ((toString (Std.format r.obligation)).length < 1000)}"

end Strata.WPVerdictTest
