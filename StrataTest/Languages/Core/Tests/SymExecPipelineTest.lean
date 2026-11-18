/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import StrataTest.Languages.Core.Tests.SymExecTestSupport
import StrataDDM.Integration.Lean.HashCommands

/-! # Symbolic execution (`--vcgen symexec`) in the verification pipeline

* End to end: `Strata.Core.verifyProgram` with `symExec` set, once per merge mode, on a program
  with two branches, an assert that fails on one of them and a cover. The default order picks
  `symExecPipelinePhase` in place of symbolic evaluation, and common subexpression elimination
  after it (under `per-path` only on a program with a large expression).
* Checks no path reaches (an `exit` jumps past them) get a result each.
* The path limit: a procedure with more than 10,000 paths is an error, with a hint that depends
  on the merge mode. The branches of an `if` whose `exit`s leave it meet at the end of the
  innermost block around it that the `exit`s do not leave.
* Checks without source ranges, on programs built as syntax trees: checks that share a label
  and metadata keep their own results; the per-path results of a check that is the only one
  with its label and metadata are grouped.
* The facts `symExecPipelinePhase` and the common subexpression elimination after it claim:
  the default order with `symExec` set, cut right after the phase, followed by the
  `assert<Fact>` phase (`Core.assertPhaseFor`) for every fact the phase claims to establish,
  and for every fact it claims to preserve that held before it; each fact it requires is
  checked on its input. The program has two procedures, nested `if`s, an early `exit`, an
  axiom and a lemma.
* The claims of every phase of the default order with `symExec` set, in each merge mode, on a
  program with a CFG procedure that calls a procedure and uses a partial function, and a
  structured procedure that calls it.
-/

meta section

namespace Strata.SymExecPipelineTest

private def parse (p : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

/-- The options of a `--vcgen symexec` run under merge mode `mode`. -/
private def symOpts (mode : Core.MergeMode) : Core.VerifyOptions :=
  { Core.VerifyOptions.quiet with symExec := some mode }

/-- Run `phases` on `prog`: the output program and the statistics the phases recorded, or the
    error. -/
private def runPhasesStats (prog : Core.Program) (phases : List Core.PipelinePhase) :
    Except String (Core.Program × _root_.Statistics) :=
  let step (p : Core.Program) (ph : Core.PipelinePhase) :
      Core.Transform.CoreTransformM Core.Program := do
    let (_, out) ← ph.transform p
    return out
  match (phases.foldlM step prog).run .emp with
  | (.ok out, σ) => .ok (out, σ.statistics)
  | (.error e, _) => .error e.message

/-- Run `phases` on `prog`: the output program, or the error. -/
private def runPhases (prog : Core.Program) (phases : List Core.PipelinePhase) :
    Except String Core.Program :=
  (runPhasesStats prog phases).map (·.1)

/-! ## End to end -/

/-- The phases the default order of `mode` runs after nondeterminism elimination. -/
private def vcPhases (mode : Core.MergeMode) : List String :=
  ((Core.corePipelinePhases (symOpts mode)).map Core.phaseName).dropWhile (· != "symExec")

#guard vcPhases .never == ["symExec", "betaReduce", "commonSubexprElim"]
#guard vcPhases (.pathsAbove 2) == ["symExec", "betaReduce", "commonSubexprElim"]
#guard vcPhases .always == ["symExec", "betaReduce", "commonSubexprElim"]

/-- Two branches; `pos` fails on the else branch; `big` is reachable. -/
private def branchPgm :=
#strata
program Core;
procedure P(x : int, out r : int) {
  if (int.gt(x, 0)) { r := 1; } else { r := 0; }
  assert [pos]: int.gt(r, 0);
  cover [big]: int.gt(x, 5);
};
#end

-- The verdicts agree across modes (`verify` reports one result per label); the modes differ in
-- the paths, obligations and merges: `pathsAbove 2` does not merge at the one join, where only 2
-- paths exist.
/-- The paths, obligations and merges of symbolic execution in the default order of `mode` on
    `pgm`, then each result of verifying it under `mode`. -/
private def verifyPgmIn (pgm : StrataDDM.Program) (mode : Core.MergeMode) : IO Unit := do
  match runPhasesStats (parse pgm) (Core.corePipelinePhases (symOpts mode)) with
  | .ok (_, st) => IO.println s!"paths {st.get "SymExec.paths"}, obligations \
      {st.get "SymExec.obligations"}, merges {st.get "SymExec.merges"}"
  | .error e => IO.println s!"error: {e}"
  match ← (Strata.Core.verifyProgram (parse pgm) (symOpts mode)).toBaseIO with
  | .ok results => for r in results do IO.println (Std.format r)
  | .error e => IO.println s!"error: {e}"

/-- `verifyPgmIn` on `branchPgm`. -/
private def verifyIn (mode : Core.MergeMode) : IO Unit := verifyPgmIn branchPgm mode

/--
info: paths 2, obligations 4, merges 0
Obligation: pos
Property: assert
Result: ❌ fail
Obligation: big
Property: cover
Result: ✅ pass
-/
#guard_msgs in
#eval verifyIn .never

/--
info: paths 1, obligations 2, merges 1
Obligation: pos
Property: assert
Result: ❌ fail
Obligation: big
Property: cover
Result: ✅ pass
-/
#guard_msgs in
#eval verifyIn .always

/--
info: paths 2, obligations 4, merges 0
Obligation: pos
Property: assert
Result: ❌ fail
Obligation: big
Property: cover
Result: ✅ pass
-/
#guard_msgs in
#eval verifyIn (.pathsAbove 2)

/-! ## Checks no path reaches -/

/-- An assert and a cover that an `exit` always jumps past. -/
private def exitSkipsPgm :=
#strata
program Core;
procedure P(x : int, out r : int) {
  b: { exit b; assert [sk]: int.gt(x, 0); cover [skc]: int.gt(x, 0); }
};
#end

-- No path reaches either check: `--vcgen symexec` gives each a result, unreachable, which fails the
-- cover. The symbolic evaluator gives neither a result.
/-- info: "sk: ✅ pass\nskc: ❌ fail" -/
#guard_msgs in
#eval SymExecTestSupport.verifyLines (parse exitSkipsPgm) (symOpts .never)
/-- info: "" -/
#guard_msgs in
#eval SymExecTestSupport.verifyLines (parse exitSkipsPgm) Core.VerifyOptions.quiet

/-! ## The path limit -/

/-- 14 sequential symbolic ifs: 2^14 = 16384 ways through. -/
private def manyPathsPgm :=
#strata
program Core;
procedure P(x : int, out r : int) {
  r := 0;
  if (int.gt(x, 0)) { r := int.add(r, 1); } else { r := int.mul(r, 2); }
  if (int.gt(x, 1)) { r := int.add(r, 1); } else { r := int.mul(r, 2); }
  if (int.gt(x, 2)) { r := int.add(r, 1); } else { r := int.mul(r, 2); }
  if (int.gt(x, 3)) { r := int.add(r, 1); } else { r := int.mul(r, 2); }
  if (int.gt(x, 4)) { r := int.add(r, 1); } else { r := int.mul(r, 2); }
  if (int.gt(x, 5)) { r := int.add(r, 1); } else { r := int.mul(r, 2); }
  if (int.gt(x, 6)) { r := int.add(r, 1); } else { r := int.mul(r, 2); }
  if (int.gt(x, 7)) { r := int.add(r, 1); } else { r := int.mul(r, 2); }
  if (int.gt(x, 8)) { r := int.add(r, 1); } else { r := int.mul(r, 2); }
  if (int.gt(x, 9)) { r := int.add(r, 1); } else { r := int.mul(r, 2); }
  if (int.gt(x, 10)) { r := int.add(r, 1); } else { r := int.mul(r, 2); }
  if (int.gt(x, 11)) { r := int.add(r, 1); } else { r := int.mul(r, 2); }
  if (int.gt(x, 12)) { r := int.add(r, 1); } else { r := int.mul(r, 2); }
  if (int.gt(x, 13)) { r := int.add(r, 1); } else { r := int.mul(r, 2); }
  assert [nonneg]: int.ge(r, 0);
};
#end

-- Over the path limit of 10,000 the run stops with an error naming the procedure and the limit
-- under `--vcgen symexec:per-path`; `merge-above:N` merges and stays under it.
/--
info: ❌ Symbolic execution error.
symExec: procedure 'P': the path limit was reached (more than 10000 paths; merge paths with
  --vcgen symexec:merge-above:N or --vcgen symexec:merged)
-/
#guard_msgs (whitespace := lax) in
#eval
  match runPhases (parse manyPathsPgm) (Core.corePipelinePhases (symOpts .never)) with
  | .ok _ => IO.println "ok"
  | .error e => IO.println e
/-- info: paths 4 -/
#guard_msgs in
#eval
  match runPhasesStats (parse manyPathsPgm) (Core.corePipelinePhases (symOpts (.pathsAbove 4)))
  with
  | .ok (_, st) => IO.println s!"paths {st.get "SymExec.paths"}"
  | .error e => IO.println e
-- `merge-above:N` with N above the limit merges nowhere below it: the error suggests a
-- smaller N.
/--
info: ❌ Symbolic execution error.
symExec: procedure 'P': the path limit was reached (more than 10000 paths; merge more paths with
  a smaller N or --vcgen symexec:merged)
-/
#guard_msgs (whitespace := lax) in
#eval
  match runPhases (parse manyPathsPgm) (Core.corePipelinePhases (symOpts (.pathsAbove 20000)))
  with
  | .ok _ => IO.println "ok"
  | .error e => IO.println e

/-- `manyPathsPgm` with each `if` in a block that its then-branch exits: the branches meet at the
    end of the block. -/
private def exitPathsPgm :=
#strata
program Core;
procedure P(x : int, out r : int) {
  r := 0;
  b0: { if (int.gt(x, 0)) { r := int.add(r, 1); exit b0; } else { r := int.mul(r, 2); } }
  b1: { if (int.gt(x, 1)) { r := int.add(r, 1); exit b1; } else { r := int.mul(r, 2); } }
  b2: { if (int.gt(x, 2)) { r := int.add(r, 1); exit b2; } else { r := int.mul(r, 2); } }
  b3: { if (int.gt(x, 3)) { r := int.add(r, 1); exit b3; } else { r := int.mul(r, 2); } }
  b4: { if (int.gt(x, 4)) { r := int.add(r, 1); exit b4; } else { r := int.mul(r, 2); } }
  b5: { if (int.gt(x, 5)) { r := int.add(r, 1); exit b5; } else { r := int.mul(r, 2); } }
  b6: { if (int.gt(x, 6)) { r := int.add(r, 1); exit b6; } else { r := int.mul(r, 2); } }
  b7: { if (int.gt(x, 7)) { r := int.add(r, 1); exit b7; } else { r := int.mul(r, 2); } }
  b8: { if (int.gt(x, 8)) { r := int.add(r, 1); exit b8; } else { r := int.mul(r, 2); } }
  b9: { if (int.gt(x, 9)) { r := int.add(r, 1); exit b9; } else { r := int.mul(r, 2); } }
  b10: { if (int.gt(x, 10)) { r := int.add(r, 1); exit b10; } else { r := int.mul(r, 2); } }
  b11: { if (int.gt(x, 11)) { r := int.add(r, 1); exit b11; } else { r := int.mul(r, 2); } }
  b12: { if (int.gt(x, 12)) { r := int.add(r, 1); exit b12; } else { r := int.mul(r, 2); } }
  b13: { if (int.gt(x, 13)) { r := int.add(r, 1); exit b13; } else { r := int.mul(r, 2); } }
  assert [nonneg]: int.ge(r, 0);
};
#end

-- Under `merged` the branches of each `if` merge at the end of its block.
/--
info: paths 1, obligations 1, merges 14
Obligation: nonneg
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verifyPgmIn exitPathsPgm .always
-- Under `per-path` the run is over the limit.
/--
info: ❌ Symbolic execution error.
symExec: procedure 'P': the path limit was reached (more than 10000 paths; merge paths with
  --vcgen symexec:merge-above:N or --vcgen symexec:merged)
-/
#guard_msgs (whitespace := lax) in
#eval
  match runPhases (parse exitPathsPgm) (Core.corePipelinePhases (symOpts .never)) with
  | .ok _ => IO.println "ok"
  | .error e => IO.println e

/-- An `exit` past the end of the `if`'s block: the branches meet at the end of `outer`, after
    the path that stays in `outer` has run `r := r + 10`. -/
private def exitOuterPgm :=
#strata
program Core;
procedure P(x : int, out r : int) {
  r := 0;
  outer: {
    inner: { if (int.gt(x, 0)) { r := 1; exit outer; } else { r := 2; } }
    r := int.add(r, 10);
  }
  assert [r_val]: (r == 1) || (r == 12);
  assert [r_big]: int.gt(r, 5);
};
#end

/--
info: paths 1, obligations 2, merges 1
Obligation: r_val
Property: assert
Result: ✅ pass
Obligation: r_big
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verifyPgmIn exitOuterPgm .always
/--
info: paths 2, obligations 4, merges 0
Obligation: r_val
Property: assert
Result: ✅ pass
Obligation: r_big
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verifyPgmIn exitOuterPgm .never

/-- `exit`s nested one `if` deeper: neither branch of an outer `if` always exits, so the outer
    `if` joins at its end; the inner `if`'s then-branch always exits, but the end of `B` lies
    outside the outer `if`'s join, so the inner `if` joins at its own end. The paths that exit
    pass both joins. -/
private def nestedExitsPgm :=
#strata
program Core;
procedure P(x : int, y : int, out r : int) {
  r := 0;
  B: {
    if (int.gt(x, 0)) { if (int.gt(y, 0)) { exit B; } else { } r := int.add(r, 1); }
      else { r := int.mul(r, 2); }
    if (int.gt(x, 1)) { if (int.gt(y, 1)) { exit B; } else { } r := int.add(r, 1); }
      else { r := int.mul(r, 2); }
    if (int.gt(x, 2)) { if (int.gt(y, 2)) { exit B; } else { } r := int.add(r, 1); }
      else { r := int.mul(r, 2); }
    if (int.gt(x, 3)) { if (int.gt(y, 3)) { exit B; } else { } r := int.add(r, 1); }
      else { r := int.mul(r, 2); }
  }
  assert [nonneg]: int.ge(r, 0);
};
#end

/--
info: paths 5, obligations 5, merges 4
Obligation: nonneg
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verifyPgmIn nestedExitsPgm .always

/-- A branch that always exits `b` and a branch that sometimes exits the enclosing `a`: the
    branches meet at the end of `b`, where the path that exited `b` and the path that stayed
    merge; the path that exits `a` passes the join. -/
private def exitTwoBlocksPgm :=
#strata
program Core;
procedure P(x : int, y : int, out r : int) {
  r := 0;
  a: {
    b: {
      if (int.gt(x, 0)) { r := 1; exit b; }
      else { if (int.gt(y, 0)) { r := 2; exit a; } else { r := 3; } }
    }
    r := int.add(r, 10);
  }
  assert [r_val]: (r == 11) || (r == 2) || (r == 13);
};
#end

/--
info: paths 2, obligations 2, merges 1
Obligation: r_val
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verifyPgmIn exitTwoBlocksPgm .always

/-! ## Common subexpression elimination under `per-path`

Under `per-path` common subexpression elimination runs only on a program with an expression
whose tree has more than `Core.symExecPerPathCSETreeSize` nodes, and leaves any other program
as it is. -/

/-- `r := r + r` 17 times: one path, and a value whose tree has more than 2^17 nodes. -/
private def selfCopyPgm :=
#strata
program Core;
procedure P(x : int, out r : int) {
  r := x;
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  assert [ok]: int.ge(r, r);
};
#end

/--
info: paths 1, obligations 1, merges 0
Obligation: ok
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verifyPgmIn selfCopyPgm .never

/-- The number of common-subexpression definitions in the program the default `per-path` order
    hands the back end. -/
private def cseDefsPerPath (pgm : StrataDDM.Program) : Except String Nat :=
  (runPhases (parse pgm) (Core.corePipelinePhases (symOpts .never))).map fun p =>
    ((toString (Std.format p)).splitOn "var $__cse.").length - 1

#guard (cseDefsPerPath selfCopyPgm).toOption == some 17

-- At the bound: after 13 doublings the largest expression has 65,533 nodes, below
-- `Core.symExecPerPathCSETreeSize`; after 14 it has 131,069, above it.
/-- `r := r + r` 13 times. -/
private def selfCopy13Pgm :=
#strata
program Core;
procedure P(x : int, out r : int) {
  r := x;
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  assert [ok]: int.ge(r, r);
};
#end

#guard (cseDefsPerPath selfCopy13Pgm).toOption == some 0

/-- `r := r + r` 14 times. -/
private def selfCopy14Pgm :=
#strata
program Core;
procedure P(x : int, out r : int) {
  r := x;
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  assert [ok]: int.ge(r, r);
};
#end

#guard (cseDefsPerPath selfCopy14Pgm).toOption == some 14

/-- A duplicate subexpression in an ordinary program: `x + 1` twice. -/
private def smallDupPgm :=
#strata
program Core;
procedure P(x : int) {
  assume [pos]: int.gt(int.add(x, 1), 0);
  assert [pos2]: int.gt(int.add(x, 1), 0);
};
#end

-- No expression is large, so the program after the gated phase is the program before it.
#guard (cseDefsPerPath smallDupPgm).toOption == some 0
#guard
  let phases := Core.corePipelinePhases (symOpts .never)
  ((runPhases (parse smallDupPgm) phases).map (toString ∘ Std.format)).toOption ==
    ((runPhases (parse smallDupPgm) phases.dropLast).map (toString ∘ Std.format)).toOption

/-! ## Checks without source ranges

The programs below are built as syntax trees, so no command carries a source range (every
metadata is `#[]`). Checks that share a label and metadata keep their own results, as in the
legacy run. A check that is the only one in the program with its label and metadata has its
per-path results grouped into one. -/

/-- Location of the expressions these tests build. -/
private abbrev testLoc : _root_.ExprSourceLoc := _root_.ExprSourceLoc.synthesized "test"

open _root_.Core Lambda Imperative in
/-- The integer variable `n`. -/
private def rv (n : String) : Expression.Expr := .fvar testLoc ⟨n, ()⟩ (some .int)

open _root_.Core Lambda Imperative in
/-- The integer literal `k`. -/
private def rint (k : Int) : Expression.Expr := .intConst testLoc k

open _root_.Core Lambda Imperative in
/-- `a > b`. -/
private def rgt (a b : Expression.Expr) : Expression.Expr := .app testLoc (.app testLoc intGtOp a) b

open _root_.Core Lambda Imperative in
/-- `a < b`. -/
private def rlt (a b : Expression.Expr) : Expression.Expr := .app testLoc (.app testLoc intLtOp a) b

open _root_.Core Lambda Imperative in
/-- A procedure `name(x : int, out r : int)` with no contract and body `body`. -/
private def rproc (name : String) (body : List Statement) : Decl :=
  .proc { header := { name := ⟨name, ()⟩, typeArgs := [], inputs := [(⟨"x", ()⟩, .int)],
                      outputs := [(⟨"r", ()⟩, .int)] }
          spec := { preconditions := [], postconditions := [] }
          body := .structured body } #[]

open _root_.Core Imperative in
/-- `P1 { assume x > 0; cover [c]: x < 0 }` and `P2 { cover [c]: x > 0 }`. -/
private def twoProcs : Core.Program :=
  { decls := [rproc "P1" [Statement.assume "a" (rgt (rv "x") (rint 0)) #[],
                          Statement.cover "c" (rlt (rv "x") (rint 0)) #[]],
              rproc "P2" [Statement.cover "c" (rgt (rv "x") (rint 0)) #[]]] }

-- No state satisfies P1's cover, so it fails; P2's passes.
/-- info: "c: ❌ fail\nc: ✅ pass" -/
#guard_msgs in
#eval SymExecTestSupport.verifyLines twoProcs Core.VerifyOptions.quiet
/-- info: "c: ❌ fail\nc: ✅ pass" -/
#guard_msgs in
#eval SymExecTestSupport.verifyLines twoProcs (symOpts .never)
/-- info: "c: ❌ fail\nc: ✅ pass" -/
#guard_msgs in
#eval SymExecTestSupport.verifyLines twoProcs (symOpts .always)

open _root_.Core Imperative in
/-- `P { if (x > 0) { cover [c]: x < 0 }; cover [c]: x > 5 }`. -/
private def oneProc : Core.Program :=
  { decls := [rproc "P" [.ite (.det (rgt (rv "x") (rint 0)))
                           [Statement.cover "c" (rlt (rv "x") (rint 0)) #[]] [] #[],
                         Statement.cover "c" (rgt (rv "x") (rint 5)) #[]]] }

-- No state satisfies the cover in the `if`, so it fails. The last cover holds on the then
-- path only: `never` gives it one result per path, `always` merges the paths first.
/-- info: "c: ❌ fail\nc: ✅ pass" -/
#guard_msgs in
#eval SymExecTestSupport.verifyLines oneProc Core.VerifyOptions.quiet
/-- info: "c: ❌ fail\nc: ✅ pass\nc: ❌ fail" -/
#guard_msgs in
#eval SymExecTestSupport.verifyLines oneProc (symOpts .never)
/-- info: "c: ❌ fail\nc: ✅ pass" -/
#guard_msgs in
#eval SymExecTestSupport.verifyLines oneProc (symOpts .always)

open _root_.Core Imperative in
/-- `P1 { assert [a]: x > 0 }` and `P2 { assert [a]: x > x }`. -/
private def twoAsserts : Core.Program :=
  { decls := [rproc "P1" [Statement.assert "a" (rgt (rv "x") (rint 0)) #[]],
              rproc "P2" [Statement.assert "a" (rgt (rv "x") (rv "x")) #[]]] }

-- Both asserts fail, each with a result of its own.
/-- info: "a: ❌ fail\na: ❌ fail" -/
#guard_msgs in
#eval SymExecTestSupport.verifyLines twoAsserts Core.VerifyOptions.quiet
/-- info: "a: ❌ fail\na: ❌ fail" -/
#guard_msgs in
#eval SymExecTestSupport.verifyLines twoAsserts (symOpts .never)

open _root_.Core Lambda Imperative in
/-- `if (x>0) { r:=1 } else { r:=0 }; cover [c]: r>0`, built as a syntax tree, so the cover
    carries empty metadata and no source range. It is the program's only check with label `c`
    and that metadata, so its per-path results are grouped by them. -/
private def oneRangelessCover : Core.Program :=
  { decls := [rproc "P" [.ite (.det (rgt (rv "x") (rint 0)))
                           [Statement.set ⟨"r", ()⟩ (rint 1) #[]]
                           [Statement.set ⟨"r", ()⟩ (rint 0) #[]] #[],
                         Statement.cover "c" (rgt (rv "r") (rint 0)) #[]]] }

-- The cover is satisfiable on the then-path, so its one result passes.
/-- info: "c: ✅ pass (fail on 1 path, pass on 1 path)" -/
#guard_msgs in
#eval SymExecTestSupport.verifyLines oneRangelessCover (symOpts .never)
/-- info: "c: ✅ pass" -/
#guard_msgs in
#eval SymExecTestSupport.verifyLines oneRangelessCover Core.VerifyOptions.quiet

/-! ## The facts the `symExec` phase and the common subexpression elimination after it claim -/

/-- Whether the `assert<f>` phase passes when run after `phases` on `prog`: `none` when `f` has
    no executable check (no `assert` form). -/
private def assertAfter (prog : Core.Program) (phases : List Core.PipelinePhase)
    (f : Core.ProgramFact) : Option Bool :=
  (Core.assertPhaseFor f.assertPhaseName).map fun a => (runPhases prog (phases ++ [a])).isOk

-- `typeAnnotated` has no executable check, so its claim is reported as `no check`.
/-- For `prog` and the default order under `mode`, cut after the phase named `name`: one line
    per fact that phase claims, `<fact> required: <verdict>` (checked on its input),
    `<fact> established: <verdict>` or `<fact> preserved: <before> -> <after>`, where a
    verdict is `holds`, `fails` or `no check`. Ends with `all claims hold` or
    `CLAIM FAILS: <facts>`. -/
private def claimedFacts (prog : Core.Program) (mode : Core.MergeMode)
    (name : String := "symExec") : IO Unit := do
  let phases := Core.corePipelinePhases (symOpts mode)
  let i := phases.findIdx (Core.phaseName · == name)
  match phases[i]? with
  | none => IO.println s!"no {name} phase"
  | some ph =>
    -- The pipeline up to the phase must itself run, or every check below fails vacuously.
    match runPhases prog (phases.take (i + 1)) with
    | .error e => IO.println s!"error: {e}"
    | .ok _ =>
      let verdict : Option Bool → String
        | some true => "holds" | some false => "fails" | none => "no check"
      let mut failed : List String := []
      for f in Strata.Pipeline.factsOf ph.requires do
        let before := assertAfter prog (phases.take i) f
        IO.println s!"{f.name} required: {verdict before}"
        if before == some false then failed := failed ++ [f.name]
      for f in Strata.Pipeline.factsOf ph.establishes do
        let after := assertAfter prog (phases.take (i + 1)) f
        IO.println s!"{f.name} established: {verdict after}"
        if after == some false then failed := failed ++ [f.name]
      for f in Strata.Pipeline.factsOf ph.preserves do
        let before := assertAfter prog (phases.take i) f
        let after := assertAfter prog (phases.take (i + 1)) f
        IO.println s!"{f.name} preserved: {verdict before} -> {verdict after}"
        if before == some true && after == some false then failed := failed ++ [f.name]
      IO.println (if failed.isEmpty then "all claims hold" else s!"CLAIM FAILS: {failed}")

/-- Two procedures, nested `if`s, an early `exit`, an axiom and a lemma. -/
private def factsPgm :=
#strata
program Core;
function f(x : int) : int;
axiom [f_pos]: forall x : int :: int.gt(f(x), 0);
lemma [f_nonneg]: forall x : int :: int.ge(f(x), 0);
procedure P(x : int, out r : int)
spec { ensures [post]: int.ge(r, 0); }
{
  b: {
    if (int.gt(x, 0)) {
      if (int.gt(x, 5)) { r := f(x); exit b; } else { r := 2; }
    } else { r := 3; }
    assert [a]: int.gt(r, 0);
  }
};
procedure Q(y : int, out s : int) {
  if (int.lt(y, 0)) { s := int.neg(y); } else { s := y; }
  assert [q]: int.ge(s, 0);
};
#end

/--
info: noCalls required: holds
noLoops required: holds
noNondetGuards required: holds
noPolymorphicProcedures required: holds
typeAnnotated required: no check
exitsCovered required: holds
noCFGBodies established: holds
staticSingleAssignment established: holds
hasObligationForm established: holds
noProcedureContracts established: holds
noInits established: holds
noCalls preserved: holds -> holds
noLoops preserved: holds -> holds
noLoopInvariants preserved: holds -> holds
noLoopMeasures preserved: holds -> holds
noPrecondsFromFuncs preserved: holds -> holds
noPolymorphicProcedures preserved: holds -> holds
noPolymorphicFunctions preserved: holds -> holds
typeAnnotated preserved: no check -> no check
exitsCovered preserved: holds -> holds
all claims hold
-/
#guard_msgs in
#eval claimedFacts (parse factsPgm) .never

/--
info: noCalls required: holds
noLoops required: holds
noNondetGuards required: holds
noPolymorphicProcedures required: holds
typeAnnotated required: no check
exitsCovered required: holds
noCFGBodies established: holds
staticSingleAssignment established: holds
hasObligationForm established: holds
noProcedureContracts established: holds
noInits established: holds
noCalls preserved: holds -> holds
noLoops preserved: holds -> holds
noLoopInvariants preserved: holds -> holds
noLoopMeasures preserved: holds -> holds
noPrecondsFromFuncs preserved: holds -> holds
noPolymorphicProcedures preserved: holds -> holds
noPolymorphicFunctions preserved: holds -> holds
typeAnnotated preserved: no check -> no check
exitsCovered preserved: holds -> holds
all claims hold
-/
#guard_msgs in
#eval claimedFacts (parse factsPgm) .always

/--
info: noCalls required: holds
noLoops required: holds
noNondetGuards required: holds
noPolymorphicProcedures required: holds
typeAnnotated required: no check
exitsCovered required: holds
noCFGBodies established: holds
staticSingleAssignment established: holds
hasObligationForm established: holds
noProcedureContracts established: holds
noInits established: holds
noCalls preserved: holds -> holds
noLoops preserved: holds -> holds
noLoopInvariants preserved: holds -> holds
noLoopMeasures preserved: holds -> holds
noPrecondsFromFuncs preserved: holds -> holds
noPolymorphicProcedures preserved: holds -> holds
noPolymorphicFunctions preserved: holds -> holds
typeAnnotated preserved: no check -> no check
exitsCovered preserved: holds -> holds
all claims hold
-/
#guard_msgs in
#eval claimedFacts (parse factsPgm) (.pathsAbove 2)

-- Common subexpression elimination after symbolic execution, under each mode that merges.
/--
info: noCFGBodies required: holds
staticSingleAssignment required: holds
typeAnnotated required: no check
noInits required: holds
noCFGBodies preserved: holds -> holds
noCalls preserved: holds -> holds
noLoops preserved: holds -> holds
noLoopInvariants preserved: holds -> holds
noLoopMeasures preserved: holds -> holds
staticSingleAssignment preserved: holds -> holds
noBetaRedexes preserved: holds -> holds
noPrecondsFromFuncs preserved: holds -> holds
noNondetGuards preserved: fails -> fails
hasObligationForm preserved: holds -> holds
noProcedureContracts preserved: holds -> holds
noPolymorphicProcedures preserved: holds -> holds
noPolymorphicFunctions preserved: holds -> holds
typeAnnotated preserved: no check -> no check
exitsCovered preserved: holds -> holds
all claims hold
-/
#guard_msgs in
#eval claimedFacts (parse factsPgm) (.pathsAbove 2) "commonSubexprElim"

/--
info: noCFGBodies required: holds
staticSingleAssignment required: holds
typeAnnotated required: no check
noInits required: holds
noCFGBodies preserved: holds -> holds
noCalls preserved: holds -> holds
noLoops preserved: holds -> holds
noLoopInvariants preserved: holds -> holds
noLoopMeasures preserved: holds -> holds
staticSingleAssignment preserved: holds -> holds
noBetaRedexes preserved: holds -> holds
noPrecondsFromFuncs preserved: holds -> holds
noNondetGuards preserved: fails -> fails
hasObligationForm preserved: holds -> holds
noProcedureContracts preserved: holds -> holds
noPolymorphicProcedures preserved: holds -> holds
noPolymorphicFunctions preserved: holds -> holds
typeAnnotated preserved: no check -> no check
exitsCovered preserved: holds -> holds
all claims hold
-/
#guard_msgs in
#eval claimedFacts (parse factsPgm) .always "commonSubexprElim"

/-! ## The claims of every phase on a CFG program -/

/-- For each phase of the default order under `mode`, on `prog`: `<phase>: all claims hold`, or
    `<phase>: CLAIM FAILS: <facts>`, a fact failing when the phase requires it and it fails on
    the phase's input, establishes it and it fails on the output, or preserves it and it holds
    on the input only. Stops at the first phase that fails to run. -/
private def allClaims (prog : Core.Program) (mode : Core.MergeMode) : IO Unit := do
  let phases := Core.corePipelinePhases (symOpts mode)
  let holds (p : Core.Program) (f : Core.ProgramFact) : Option Bool :=
    (Core.assertPhaseFor f.assertPhaseName).map fun a => (runPhases p [a]).isOk
  for (ph, i) in phases.zipIdx do
    match runPhases prog (phases.take i), runPhases prog (phases.take (i + 1)) with
    | .ok inp, .ok out =>
      let failed :=
        (Strata.Pipeline.factsOf ph.requires).filter (holds inp · == some false) ++
        (Strata.Pipeline.factsOf ph.establishes).filter (holds out · == some false) ++
        (Strata.Pipeline.factsOf ph.preserves).filter fun f =>
          holds inp f == some true && holds out f == some false
      IO.println s!"{Core.phaseName ph}: {if failed.isEmpty then "all claims hold"
        else s!"CLAIM FAILS: {failed.map (·.name)}"}"
    | .error e, _ | _, .error e =>
      IO.println s!"{Core.phaseName ph}: error: {e}"
      return

/-- A CFG procedure with two calls to a procedure with a contract and no body, and a partial
    function in a command and in a branch condition, and a structured procedure calling it. -/
private def cfgFactsPgm :=
#strata
program Core;
procedure Inc(x : int, out y : int)
spec { requires [inc_pre]: int.ge(x, 0); free ensures [inc_post]: y == int.add(x, 1); };
procedure P(a : int, b : int, out r : int)
spec { requires [a_nneg]: int.ge(a, 0); ensures [r_pos]: int.gt(r, 0); }
cfg entry {
  entry: { call Inc(a, out r); r := int.add(r, int.safeDiv(a, b));
    branch (int.gt(int.safeDiv(r, b), 0)) goto pos else goto neg; }
  pos: { call Inc(r, out r); goto done; }
  neg: { r := 1; goto done; }
  done: { assert [r_nz]: !(r == 0); return; }
};
procedure Q(x : int, out s : int) {
  if (int.ge(x, 0)) { call P(x, 1, out s); } else { s := 1; }
  assert [s_pos]: int.gt(s, 0);
};
#end

/--
info: typeCheck: all claims hold
callElim: all claims hold
termCheck: all claims hold
precondElim: all claims hold
seqTotalize: all claims hold
insertLoopInvariantAsserts: all claims hold
loopElim: all claims hold
genOpaqueTypeParams: all claims hold
monomorphizeFunctions: all claims hold
simplify: all claims hold
nondetElim: all claims hold
symExec: all claims hold
betaReduce: all claims hold
commonSubexprElim: all claims hold
-/
#guard_msgs in
#eval allClaims (parse cfgFactsPgm) .never

/--
info: typeCheck: all claims hold
callElim: all claims hold
termCheck: all claims hold
precondElim: all claims hold
seqTotalize: all claims hold
insertLoopInvariantAsserts: all claims hold
loopElim: all claims hold
genOpaqueTypeParams: all claims hold
monomorphizeFunctions: all claims hold
simplify: all claims hold
nondetElim: all claims hold
symExec: all claims hold
betaReduce: all claims hold
commonSubexprElim: all claims hold
-/
#guard_msgs in
#eval allClaims (parse cfgFactsPgm) .always

/--
info: typeCheck: all claims hold
callElim: all claims hold
termCheck: all claims hold
precondElim: all claims hold
seqTotalize: all claims hold
insertLoopInvariantAsserts: all claims hold
loopElim: all claims hold
genOpaqueTypeParams: all claims hold
monomorphizeFunctions: all claims hold
simplify: all claims hold
nondetElim: all claims hold
symExec: all claims hold
betaReduce: all claims hold
commonSubexprElim: all claims hold
-/
#guard_msgs in
#eval allClaims (parse cfgFactsPgm) (.pathsAbove 2)

end Strata.SymExecPipelineTest

end -- meta section
