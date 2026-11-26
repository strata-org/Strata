/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.SymExecTree
meta import Strata.Languages.Core.ObligationExtraction
meta import Strata.Languages.Core.SymExecReplay
meta import Strata.Languages.Core.Verifier
meta import Strata.SimpleAPI
meta import StrataTest.Languages.Core.Tests.SymExecTestSupport
import StrataDDM.Integration.Lean.HashCommands

/-! # Behavioural tests of symbolic execution on the monadic interpreter (`Core.SymExec`)

Each test program is Core source, translated and type-checked as the verifier does before
VC generation (`procOf`). A program that fails type checking gives no procedure, so every check
on it fails (`run` gives `none`) rather than passing on an empty one. A few programs are built
as syntax trees, where the type checker rejects the case (an unbound variable, an `exit` no
block matches).
-/

meta section

namespace SymExecTest

open Core Core.SymExec Lambda Imperative SymExecTestSupport

-- Builders for the test programs that are built as syntax trees.
private abbrev testLoc : ExprSourceLoc := ExprSourceLoc.synthesized "test"
private def id (name : String) : CoreIdent := ⟨name, ()⟩
private def int (n : Int) : Expression.Expr := .intConst testLoc n
private def md : MetaData Expression := #[]
private def v (name : String) : Expression.Expr := .fvar testLoc (id name) (some .int)
private def bin (op : Expression.Expr) (a b : Expression.Expr) : Expression.Expr :=
  .app testLoc (.app testLoc op a) b
private def gt (a b : Expression.Expr) := bin intGtOp a b

private def setR (e : Expression.Expr) : Statement := Statement.set (id "r") e md
private def ifS (c : Expression.Expr) (t e : List Statement) : Statement := .ite (.det c) t e md

/-- `procedure P(x : int) returns (r : int) { body }`, as a syntax tree. -/
private def proc (body : List Statement) : Option Procedure :=
  some { header := { name := id "P", typeArgs := [], inputs := [(id "x", .int)],
                     outputs := [(id "r", .int)] }
         spec := { preconditions := [], postconditions := [] }
         body := .structured body false }

/-- A run's counts: paths finished, paths stopped, unmatched exits, obligations. -/
private structure Summary where
  finished : Nat
  stopped : Nat
  unmatchedExits : Nat
  obligations : Nat
  deriving Repr

/-- The counts of `run p`. -/
private def summary (p : Option Procedure) : Option Summary :=
  (run p).map fun r => ⟨r.finished, r.stopped, r.unmatchedExits, r.obligations.length⟩

/-- Print the obligations of `run p`. -/
private def obls (p : Option Procedure) : IO Unit := printObls (run p)

/-- Why each path of `run p` that neither finished nor joined ended, in node order:
    `stopped: <reason>`, `unmatchedExit <label>`, `outOfWork` or `running`. -/
private def endings (p : Option Procedure) : Option (List String) :=
  (run p).map fun r => r.nodes.toList.filterMap fun n => match n.status with
    | .stopped reason => some s!"stopped: {reason}"
    | .unmatchedExit l => some s!"unmatchedExit {l}"
    | .outOfWork => some "outOfWork"
    | .running => some "running"
    | _ => none

/-- The labels of `r`'s unreached checks, each with its path-condition labels. -/
private def unreachedLabels (r : Result) : List (String × List String) :=
  r.unreached.map fun o => (o.label, o.pc.map (·.1))

-- Straight-line code: one finished path and one obligation, stated over the input symbol
-- (`$__sym0 + 1 > $__sym0`).
private def straight := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  r := int.add(x, 1);
  assert [a]: int.gt(r, x);
};
#end
/-- info: some { finished := 1, stopped := 0, unmatchedExits := 0, obligations := 1 } -/
#guard_msgs in
#eval summary straight
/-- info: [a] under []  check: int.gt(int.add($__symx_0, 1), $__symx_0) -/
#guard_msgs in
#eval obls straight

-- Symbolic guard: two paths; each assert folds to `true` under its branch; each obligation's path
-- condition has one entry (the guard or its negation).
private def twoBranchesPgm : StrataDDM.Program :=
#strata
program Core;
procedure P(x : int, out r : int) {
  if (int.gt(x, 0)) { r := 1; } else { r := 2; }
  assert [a]: int.gt(r, 0);
};
#end
/-- The procedure of `twoBranchesPgm`. -/
private def twoBranches := procOf twoBranchesPgm
/-- info: some { finished := 2, stopped := 0, unmatchedExits := 0, obligations := 2 } -/
#guard_msgs in
#eval summary twoBranches
/--
info: [a] under [int.gt($__symx_0, 0)]  check: true
[a] under [if int.gt($__symx_0, 0) then false else true]  check: true
-/
#guard_msgs in
#eval obls twoBranches

-- A guard that folds to a literal does not fork: one path, one obligation.
private def concrete := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  if (int.gt(1, 0)) { r := 1; } else { r := 2; }
  assert [a]: int.gt(r, 0);
};
#end
/-- info: some { finished := 1, stopped := 0, unmatchedExits := 0, obligations := 1 } -/
#guard_msgs in
#eval summary concrete
/-- info: [a] under []  check: true -/
#guard_msgs in
#eval obls concrete

-- Nested symbolic guards: three paths.
private def nested := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  if (int.gt(x, 0)) {
    if (int.gt(x, 5)) { r := 1; } else { r := 2; }
  } else { r := 3; }
  assert [a]: int.gt(r, 0);
};
#end
/-- info: some { finished := 3, stopped := 0, unmatchedExits := 0, obligations := 3 } -/
#guard_msgs in
#eval summary nested
-- Node order: the root's else child (one guard) comes before the then child's children.
/--
info: [a] under [if int.gt($__symx_0, 0) then false else true]  check: true
[a] under [int.gt($__symx_0, 0), int.gt($__symx_0, 5)]  check: true
[a] under [int.gt($__symx_0, 0), if int.gt($__symx_0, 5) then false else true]  check: true
-/
#guard_msgs in
#eval obls nested

-- An obligation before the fork is stored once (on the root), not once per path.
private def before := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  assert [pre]: int.gt(x, 0);
  if (int.gt(x, 0)) { r := 1; } else { r := 2; }
};
#end
/-- info: some { finished := 2, stopped := 0, unmatchedExits := 0, obligations := 1 } -/
#guard_msgs in
#eval summary before
/-- info: [pre] under []  check: int.gt($__symx_0, 0) -/
#guard_msgs in
#eval IO.println <| ((run before).bind fun r => r.nodes[0]?.map (oblLines ·.obls.toList)).getD ""

-- Early exit: the exiting path skips the rest of the block (`r` stays 7) but still reaches the
-- postcondition; the other path sets `r := 5`, which fails `r > 6`.
private def early := procOf <|
#strata
program Core;
procedure P(x : int, out r : int)
spec { ensures [post]: int.gt(r, 6); }
{
  b: {
    if (int.gt(x, 0)) { r := 7; exit b; }
    r := 5;
  }
};
#end
/-- info: some { finished := 2, stopped := 0, unmatchedExits := 0, obligations := 2 } -/
#guard_msgs in
#eval summary early
/--
info: [post] under [int.gt($__symx_0, 0)]  check: true
[post] under [if int.gt($__symx_0, 0) then false else true]  check: false
-/
#guard_msgs in
#eval obls early

-- An exit no block matches ends its path as an unmatched exit; the other path finishes. (A
-- syntax tree: the type checker rejects an exit no block matches.)
private def unmatched := proc [ifS (gt (v "x") (int 0)) [.exit "nowhere" md] []]
/-- info: some { finished := 1, stopped := 0, unmatchedExits := 1, obligations := 0 } -/
#guard_msgs in
#eval summary unmatched
/-- info: some ["unmatchedExit nowhere"] -/
#guard_msgs in
#eval endings unmatched

-- Precondition: an assumed guard prunes the other branch (syntactically).
private def pruned := procOf <|
#strata
program Core;
procedure P(x : int, out r : int)
spec { requires [pre]: int.gt(x, 0); }
{
  if (int.gt(x, 0)) { r := 1; } else { r := 2; }
};
#end
/-- info: some { finished := 1, stopped := 0, unmatchedExits := 0, obligations := 0 } -/
#guard_msgs in
#eval summary pruned
#guard ((run pruned).map fun r => r.nodes.size) == some 1

-- A guard already in the path condition decides a later guard equal to it up to source
-- locations: the second `if` takes the branch the first one took (two paths, not four).
private def sameGuard := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  if (int.gt(x, 0)) { r := 1; } else { r := 2; }
  if (int.gt(x, 0)) { r := int.add(r, 1); } else { r := int.sub(r, 1); }
  assert [a]: int.gt(r, 0);
};
#end
/-- The guards of the top-level `if`s of `p`'s body. -/
private def topGuards (p : Option Procedure) : List Expression.Expr :=
  match (p.map (·.body) : Option Procedure.Body) with
  | some (.structured ss _) => ss.filterMap fun | .ite (.det g) _ _ _ => some g | _ => none
  | _ => []
-- The two guards differ in their source locations only.
#guard match topGuards sameGuard with
  | [g1, g2] => g1 != g2 && g1.beqIgnoringMetadata g2
  | _ => false
/-- info: some { finished := 2, stopped := 0, unmatchedExits := 0, obligations := 2 } -/
#guard_msgs in
#eval summary sameGuard
/--
info: [a] under [int.gt($__symx_0, 0)]  check: true
[a] under [if int.gt($__symx_0, 0) then false else true]  check: true
-/
#guard_msgs in
#eval obls sameGuard

-- `assume false` ends the path (unlike `--vcgen symbolic`, the legacy evaluator): no run
-- follows it, so the check after it gets no obligation (see "Ending infeasible paths").
private def assumeFalse := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  assume [f]: false;
  assert [a]: false;
};
#end
/-- info: some { finished := 0, stopped := 0, unmatchedExits := 0, obligations := 0 } -/
#guard_msgs in
#eval summary assumeFalse

-- Path-condition entries keep the `assume`'s label.
private def labelled := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  assume [callElimAssume_q]: int.gt(x, 0);
  assert [a]: true;
};
#end
#guard ((run labelled).map (·.obligations.map fun o => o.pc.map (·.1))) ==
  some [["callElimAssume_q"]]
-- An `assume` of a condition the path already has, under another label, adds an entry under its
-- own label.
private def reassumed := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  if (int.gt(x, 0)) {
    assume [$__loopElimAssume_guard_0]: int.gt(x, 0);
    assert [a]: int.gt(x, 0);
  }
};
#end
#guard ((run reassumed).map (·.obligations.map fun o => o.pc.map (·.1))) ==
  some [["$__loopElimAssume_guard_0", "<label_ite_cond_true: int.gt($__symx_0, 0)>"]]

-- A cover is recorded as an obligation of kind cover.
private def cov := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  cover [c]: int.gt(x, 3);
};
#end
#guard ((run cov).map (·.obligations.map (·.kind))) == some [.cover]
/-- info: [c] under []  check: int.gt($__symx_0, 3) -/
#guard_msgs in
#eval obls cov

-- A path that reads an unbound variable stops; the other path finishes. (A syntax tree: the
-- type checker rejects an unbound variable.)
private def stuck := proc [ifS (gt (v "x") (int 0)) [setR (v "y")] [setR (int 2)]]
/-- info: some { finished := 1, stopped := 1, unmatchedExits := 0, obligations := 0 } -/
#guard_msgs in
#eval summary stuck
/-- info: some ["stopped: an expression did not evaluate"] -/
#guard_msgs in
#eval endings stuck

-- A Boolean variable declared without a value gets a fresh symbol; the fork happens at the guard
-- that uses it.
private def havocB := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  var b : bool;
  if (b) { r := 1; } else { r := 2; }
};
#end
/-- info: some { finished := 2, stopped := 0, unmatchedExits := 0, obligations := 0 } -/
#guard_msgs in
#eval summary havocB

-- For an in-out parameter `x`, `old x` is `x`'s entry symbol, also after `x` is reassigned.
private def inout := procOf <|
#strata
program Core;
procedure P(inout x : int) {
  x := int.add(x, 1);
  assert [a]: int.gt(x, old x);
};
#end
/-- info: [a] under []  check: int.gt(int.add($__symx_0, 1), $__symx_0) -/
#guard_msgs in
#eval obls inout

-- A failing assert: its condition folds to `false` on the then-path and to `true` on the
-- else-path.
private def failing := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  if (int.gt(x, 0)) { r := 0; } else { r := 1; }
  assert [a]: int.gt(r, 0);
};
#end
/--
info: [a] under [int.gt($__symx_0, 0)]  check: false
[a] under [if int.gt($__symx_0, 0) then false else true]  check: true
-/
#guard_msgs in
#eval obls failing

-- Labels no path reaches (a dead branch) are still reported, under the path condition `false`
-- labelled with the guard, covers before asserts (as in the symbolic evaluator).
private def deadBranch := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  if (false) { assert [da]: false; cover [dc]: true; } else { assert [live]: true; }
};
#end
/-- info: [live] under []  check: true -/
#guard_msgs in
#eval obls deadBranch
/--
info: [dc] under [false]  check: false
[da] under [false]  check: true
-/
#guard_msgs in
#eval IO.println <| ((run deadBranch).map (oblLines ·.unreached)).getD "no result"
#guard (run deadBranch).map unreachedLabels ==
  some [("dc", ["<dead_branch: false>"]), ("da", ["<dead_branch: false>"])]

-- Checks an `exit` always jumps past: no path reaches them, and the complete run reports each
-- once, in body order, under the path condition `false` labelled with the check.
private def skipped := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  b: { exit b; assert [sk]: false; cover [skc]: true; }
};
#end
#guard ((run skipped).map fun r => r.obligations.length) == some 0
/--
info: [sk] under [false]  check: true
[skc] under [false]  check: false
-/
#guard_msgs in
#eval IO.println <| ((run skipped).map (oblLines ·.unreached)).getD "no result"
#guard (run skipped).map unreachedLabels ==
  some [("sk", ["<unreachable_check: sk>"]), ("skc", ["<unreachable_check: skc>"])]

-- An `exit` taken on one path only: the other path reaches the check, so it is not unreached.
private def halfSkipped := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  b: { if (int.gt(x, 0)) { exit b; } else { r := 1; } assert [half]: int.gt(r, 0); }
};
#end
#guard ((run halfSkipped).map fun r => (r.obligations.map (·.label), unreachedLabels r)) ==
  some (["half"], [])

-- A check one path skips at a decided guard (`r = 1` is `false` where `r := 0`) and another
-- path reaches is not unreached.
private def decidedOnOnePath := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  if (int.gt(x, 0)) { r := 1; } else { r := 0; }
  if (r == 1) { assert [one]: r == 1; }
};
#end
#guard ((run decidedOnOnePath).map fun r => (r.obligations.map (·.label), unreachedLabels r))
  == some (["one"], [])

-- A run that stops early reports no check past the point where it stopped: `skipped` with too
-- small a budget.
#guard ((run skipped (fuel := 2)).map fun r =>
  (r.completeness matches .notAnalyzed _, unreachedLabels r)) == some (true, [])

-- Else-pruning: the guard's negation is already assumed, so only the else branch runs. (Pruning
-- is syntactic, so the precondition is written in the form the run gives a negated guard.)
private def elsePruned := procOf <|
#strata
program Core;
procedure P(x : int, out r : int)
spec { requires [pre]: if int.gt(x, 0) then false else true; }
{
  if (int.gt(x, 0)) { r := 1; } else { r := 2; }
};
#end
/-- info: some { finished := 1, stopped := 0, unmatchedExits := 0, obligations := 0 } -/
#guard_msgs in
#eval summary elsePruned

-- An `assume` contradicting the precondition without being literal `false` does not end the
-- path: the assert after it gets an obligation, under both conditions, for the solver.
private def contra := procOf <|
#strata
program Core;
procedure P(x : int, out r : int)
spec { requires [pre]: int.gt(x, 0); }
{
  assume [n]: if int.gt(x, 0) then false else true;
  assert [a]: false;
};
#end
/-- info: some { finished := 1, stopped := 0, unmatchedExits := 0, obligations := 1 } -/
#guard_msgs in
#eval summary contra
#guard ((run contra).map (·.countStatus (· matches .infeasible _))) == some 0
#guard (run contra).map unreachedLabels == some []

-- A loop on a symbolic guard unrolls until the per-path budget (40) runs out: each loop exit is a
-- finished path (4), and both branches of the last fork stop (2). Loop invariants are not
-- checked, so there are no obligations.
private def loopPgm : StrataDDM.Program :=
#strata
program Core;
procedure P(x : int, out r : int) {
  r := x;
  while (int.gt(r, 0)) invariant [inv]: false { r := int.add(r, int.neg(1)); }
};
#end
/-- The procedure of `loopPgm`. -/
private def loopP := procOf loopPgm
#guard ((loopP.map (exploreProc {} 10000 40 Core.Factory ·)).map fun r =>
  (r.finished, r.stopped, r.outOfWork, r.obligations.length)) == some (4, 2, 0, 0)

-- The total work bound: pending paths are `outOfWork`, not stopped.
#guard ((twoBranches.map (exploreProc {} 3 1000 Core.Factory ·)).map fun r =>
  (r.outOfWork, r.stopped)) == some (2, 0)

-- Free postconditions are not checked.
private def freePost := procOf <|
#strata
program Core;
procedure P(x : int, out r : int)
spec { free ensures [fp]: false; }
{
};
#end
/-- info: some { finished := 1, stopped := 0, unmatchedExits := 0, obligations := 0 } -/
#guard_msgs in
#eval summary freePost

-- Sibling paths create distinct symbols (the counter is the explorer's).
private def siblings := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  if (int.gt(x, 0)) { var a : int; assert [pa]: int.gt(a, 0); }
  else { var b : int; assert [pb]: int.gt(b, 0); }
};
#end
/--
info: [pa] under [int.gt($__symx_0, 0)]  check: int.gt($__syma_2, 0)
[pb] under [if int.gt($__symx_0, 0) then false else true]  check: int.gt($__symb_3, 0)
-/
#guard_msgs in
#eval obls siblings

-- A program name that starts with the default prefix makes the run choose a longer one, so the
-- formal `$__sym0` is not mistaken for (or captured by) the symbol `$__sym0`.
private def clashing := procOf <|
#strata
program Core;
procedure P($__sym0 : int, out r : int) {
  r := int.add($__sym0, 1);
  assert [a]: int.gt(r, $__sym0);
};
#end
#guard choosePrefix ["$__sym0", "r"] == "$__sym_"
#guard choosePrefix ["x", "r"] == defaultSymPrefix
-- One name can rule out several extensions: every prefix of `$__sym____` up to its length.
#guard choosePrefix ["$__sym____"] == "$__sym_____"
/-- info: [a] under []  check: int.gt(int.add($__sym_$__sym0_0, 1), $__sym_$__sym0_0) -/
#guard_msgs in
#eval obls clashing

-- A call or a nondeterministic guard is not refused by `exploreProc`: it stops its path.
/-- A procedure that calls another. -/
private def callPgm : StrataDDM.Program :=
#strata
program Core;
procedure Q() { };
procedure P(x : int, out r : int) {
  call Q();
};
#end
/-- A procedure with a nondeterministic guard. -/
private def nondetPgm : StrataDDM.Program :=
#strata
program Core;
procedure P(x : int, out r : int) {
  if * { r := 1; }
};
#end
/-- info: some { finished := 0, stopped := 1, unmatchedExits := 0, obligations := 0 } -/
#guard_msgs in
#eval summary (procOf callPgm)
/-- info: some ["stopped: run interrupted: call (eliminate calls first)"] -/
#guard_msgs in
#eval endings (procOf callPgm)
/-- info: some { finished := 0, stopped := 1, unmatchedExits := 0, obligations := 0 } -/
#guard_msgs in
#eval summary (procOf nondetPgm)
/-- info: some ["stopped: expected a Boolean oracle choice"] -/
#guard_msgs in
#eval endings (procOf nondetPgm)

-- `symExecProgram` refuses a program that lacks a required fact, naming the fact.
#guard (match (progOf twoBranchesPgm).map (symExecProgram {} 10000 1000 Core.Factory) with
  | some (.ok [("P", r)]) => r.finished == 2 | _ => false)
#guard (match (progOf callPgm).map (symExecProgram {} 10000 1000 Core.Factory) with
  | some (.error fs) => fs == [.noCalls] | _ => false)
#guard (match (progOf nondetPgm).map (symExecProgram {} 10000 1000 Core.Factory) with
  | some (.error fs) => fs == [.noNondetGuards] | _ => false)
#guard (match (progOf loopPgm).map (symExecProgram {} 10000 1000 Core.Factory) with
  | some (.error fs) => fs == [.noLoops] | _ => false)

-- Obligation extraction from `treeStmts` yields the per-path obligations (same set and count),
-- each with its own path condition, a join symbol's declaration standing for its definition
-- (`newAssumes`).
/-- The equation `x == v` a declaration `init x : ty := v` stands for. -/
private def declEq (x : CoreIdent) (ty : Expression.Ty) (v : Expression.Expr) : Expression.Expr :=
  match ty with
  | .forAll _ mty => LExpr.eq symExecLoc (.fvar symExecLoc x (some mty)) v
/-- (label, assumptions, goal) per obligation, from extraction of `treeStmts`, under merge
    policy `pol`; a declaration counts as its equation (`declEq`). -/
private def viaTree (p : Option Procedure) (pol : MergePolicy := .never) :
    Option (List (String × List Expression.Expr × Expression.Expr)) :=
  (run p pol).bind fun r =>
    match ObligationExtraction.extractFromStatements ⟨[]⟩ r.treeStmts with
    | .ok obs => some (obs.toList.map fun o =>
        (o.label, o.assumptions.flatten.filterMap (fun
          | .assumption _ e => some e
          | .varDecl x ty (.det v) => some (declEq x ty v)
          | _ => none),
         o.obligation))
    | .error _ => none
/-- (label, assumptions, goal) per obligation, from the recorded paths, under merge policy
    `pol`; a join symbol's definition counts as the equation of its declaration (`newAssumes`,
    `declEq`). -/
private def viaPaths (p : Option Procedure) (pol : MergePolicy := .never) :
    Option (List (String × List Expression.Expr × Expression.Expr)) :=
  (run p pol).map fun r => r.obligations.map fun o =>
    (o.label, (newAssumes o.pc 0).filterMap (fun
        | .cmd (.cmd (.assume _ e _)) => some e
        | .cmd (.cmd (.init x ty (.det v) _)) => some (declEq x ty v)
        | _ => none),
      o.cond)
/-- `viaTree` and `viaPaths` agree as sets with equal counts, under merge policy `pol`. -/
private def sameAsPaths (p : Option Procedure) (pol : MergePolicy := .never) : Bool :=
  match viaTree p pol, viaPaths p pol with
  | some a, some b => a.length == b.length && a.all (b.contains ·) && b.all (a.contains ·)
  | _, _ => false
#guard [straight, twoBranches, nested, before, early, failing, contra, cov, siblings, inout,
  labelled].all sameAsPaths
-- Two sequential symbolic ifs with an assert after each: 2 + 4 = 6 obligations over 4 paths;
-- the tree writes 6 assumptions (one per edge) where one block per obligation writes
-- 2·1 + 4·2 = 10.
private def twoSeq := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  if (int.gt(x, 0)) { r := 1; } else { r := 2; }
  assert [a1]: int.gt(r, 0);
  if (int.gt(x, 5)) { r := int.add(r, 1); }
  assert [a2]: int.gt(r, 0);
};
#end
#guard sameAsPaths twoSeq
mutual
/-- Number of `assume`s in a statement, including inside `if` branches. -/
private def countAssumesStmt : Statement → Nat
  | .cmd (.cmd (.assume ..)) => 1
  | .ite _ t e _ => countAssumes t + countAssumes e
  | _ => 0
/-- Number of `assume`s, including inside `if` branches. -/
private def countAssumes : List Statement → Nat
  | [] => 0
  | s :: rest => countAssumesStmt s + countAssumes rest
end
#guard ((run twoSeq).map fun r => (r.obligations.length, countAssumes r.treeStmts,
  (r.obligations.map (·.pc.length)).sum)) == some (6, 6, 10)

/-! ## Merge policies -/


/-- A merging run's counts: paths finished, paths stopped, unmatched exits, obligations, joins
    merged. -/
private structure MergeSummary where
  finished : Nat
  stopped : Nat
  unmatchedExits : Nat
  obligations : Nat
  merges : Nat
  deriving Repr

/-- The counts of `run p pol`. -/
private def mergeSummary (pol : MergePolicy) (p : Option Procedure) : Option MergeSummary :=
  (run p pol).map fun r =>
    ⟨r.finished, r.stopped, r.unmatchedExits, r.obligations.length, r.merges⟩

-- Two sequential symbolic ifs: never merging gives 4 paths and 6 obligations; merging at every
-- join gives one path through each join, so a1 and a2 are each checked once.
/--
info: some { finished := 4, stopped := 0, unmatchedExits := 0, obligations := 6, merges := 0 }
-/
#guard_msgs in
#eval mergeSummary .never twoSeq
/--
info: some { finished := 1, stopped := 0, unmatchedExits := 0, obligations := 2, merges := 2 }
-/
#guard_msgs in
#eval mergeSummary .always twoSeq
-- After the first merge `r` is the join symbol `$__joinr_0`, defined as `if x > 0 then 1 else 2`;
-- the second merge's value mentions `$__joinr_0`, not a copy of that term.
/--
info: [a1] under [$__joinr_0 == (if int.gt($__symx_0, 0) then 1 else 2)]  check: int.gt($__joinr_0,
  0)
[a2] under [$__joinr_0 == (if int.gt($__symx_0, 0) then 1 else 2), $__joinr_1 == (if
  int.gt($__symx_0, 5) then int.add($__joinr_0, 1) else $__joinr_0)]  check: int.gt($__joinr_1, 0)
-/
#guard_msgs (whitespace := lax) in
#eval printObls (run twoSeq .always)
-- The merged path condition keeps each branch's labels, guarded (`if g then e else true`).
private def branchAssume := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  if (int.gt(x, 0)) { assume [callElimAssume_q]: int.gt(x, 3); r := 1; } else { r := 2; }
  assert [a]: int.gt(r, 0);
};
#end
/--
info: [a] under [if int.gt($__symx_0, 0) then int.gt($__symx_0, 3) else true, $__joinr_0 == (if
  int.gt($__symx_0, 0) then 1 else 2)]  check: int.gt($__joinr_0, 0)
-/
#guard_msgs (whitespace := lax) in
#eval printObls (run branchAssume .always)
#guard ((run branchAssume .always).map (·.obligations.map fun o => o.pc.map (·.1))) ==
  some [["<join_value: r>", "callElimAssume_q"]]
-- A fork under a non-empty path condition (the precondition) still merges: the merged path
-- condition keeps the precondition as its shared prefix.
private def mergeUnderPre := procOf <|
#strata
program Core;
procedure P(x : int, out r : int)
spec { requires [pre]: int.gt(x, 0); }
{
  if (int.gt(x, 5)) { assume [q]: int.gt(x, 7); r := 1; } else { r := 2; }
  assert [a]: int.gt(r, 0);
};
#end
/--
info: some { finished := 1, stopped := 0, unmatchedExits := 0, obligations := 1, merges := 1 }
-/
#guard_msgs in
#eval mergeSummary .always mergeUnderPre
/--
info: [a] under [int.gt($__symx_0, 0), if int.gt($__symx_0, 5) then int.gt($__symx_0, 7) else true,
  $__joinr_0 == (if int.gt($__symx_0, 5) then 1 else 2)]  check: int.gt($__joinr_0, 0)
-/
#guard_msgs (whitespace := lax) in
#eval printObls (run mergeUnderPre .always)
-- Branches that assign values equal up to source locations merge to one value, not an `if`.
private def sameValue := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  if (int.gt(x, 0)) { r := int.add(x, 1); } else { r := int.add(x, 1); }
  assert [a]: int.gt(r, 0);
};
#end
-- The two assigned values differ in their source locations only.
#guard match (sameValue.map (·.body) : Option Procedure.Body) with
  | some (.structured (.ite _ [.cmd (.cmd (.set _ (.det a) _))]
      [.cmd (.cmd (.set _ (.det b) _))] _ :: _) false) => a != b && a.beqIgnoringMetadata b
  | _ => false
/--
info: some { finished := 1, stopped := 0, unmatchedExits := 0, obligations := 1, merges := 1 }
-/
#guard_msgs in
#eval mergeSummary .always sameValue
/-- info: [a] under []  check: int.gt(int.add($__symx_0, 1), 0) -/
#guard_msgs in
#eval printObls (run sameValue .always)
-- A branch that always exits past the if: the branches meet at the end of the block it exits,
-- after the other branch has run `r := 5`.
/--
info: some { finished := 1, stopped := 0, unmatchedExits := 0, obligations := 1, merges := 1 }
-/
#guard_msgs in
#eval mergeSummary .always early
-- An exit out of two nested ifs: neither branch of the outer `if` always exits, so it joins at its
-- end. The inner `if`'s then-branch always exits `b`, but the end of `b` lies outside the outer
-- `if`'s join, so the inner `if` joins at its own end, where only its else-branch arrives. The
-- path that exits passes both joins; the outer join merges the two branches that remain.
private def nestedExit := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  b: {
    if (int.gt(x, 0)) {
      if (int.gt(x, 5)) { r := 1; exit b; } else { r := 2; }
    } else { r := 3; }
    assert [a]: int.gt(r, 0);
  }
};
#end
/--
info: some { finished := 2, stopped := 0, unmatchedExits := 0, obligations := 1, merges := 1 }
-/
#guard_msgs in
#eval mergeSummary .always nestedExit
-- A loop guard forks without opening a join; both of its paths still count inside the `if`'s
-- branches. A loop does not always exit, so the `if` joins at its end; the path that runs the loop
-- body exits past it, and the `if`'s join merges the two branches that remain.
private def loopExit := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  l: {
    if (int.gt(x, 0)) {
      while (int.gt(x, 5)) { r := 1; exit l; }
      r := 2;
    } else { r := 3; }
    assert [a]: int.gt(r, 1);
  }
};
#end
/--
info: some { finished := 2, stopped := 0, unmatchedExits := 0, obligations := 1, merges := 1 }
-/
#guard_msgs in
#eval mergeSummary .always loopExit
-- `pathsAbove 3` merges at a join once more than 3 paths would exist.
private def threeSeq := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  if (int.gt(x, 0)) { r := 1; } else { r := 2; }
  if (int.gt(x, 5)) { r := int.add(r, 1); }
  if (int.gt(x, 9)) { r := int.add(r, 1); }
  assert [a]: int.gt(r, 0);
};
#end
/--
info: some { finished := 8, stopped := 0, unmatchedExits := 0, obligations := 8, merges := 0 }
-/
#guard_msgs in
#eval mergeSummary .never threeSeq
/--
info: some { finished := 1, stopped := 0, unmatchedExits := 0, obligations := 1, merges := 3 }
-/
#guard_msgs in
#eval mergeSummary .always threeSeq
/--
info: some { finished := 3, stopped := 0, unmatchedExits := 0, obligations := 3, merges := 4 }
-/
#guard_msgs in
#eval mergeSummary (.pathsAbove 3) threeSeq
-- `pathsAbove n` counts the paths waiting at other joins. An else-if chain of depth `k`
-- (`if x > k-1 {r := k} else {if x > k-2 ... else {r := 0}}`, then a check) has `k + 1` ways
-- through; the paths waiting at the outer joins make the inner joins merge.
private def elseIfChain : Nat → Statement
  | 0 => setR (int 0)
  | k + 1 => ifS (gt (v "x") (int k)) [setR (int (k + 1))] [elseIfChain k]
/-- The else-if chain of depth `k` followed by `assert [a]: r > -1`. -/
private def deepElse (k : Nat) : Option Procedure :=
  proc [elseIfChain k, .assert "a" (gt (v "r") (int (-1))) md]
/--
info: some { finished := 7, stopped := 0, unmatchedExits := 0, obligations := 7, merges := 0 }
-/
#guard_msgs in
#eval mergeSummary .never (deepElse 6)
/--
info: some { finished := 2, stopped := 0, unmatchedExits := 0, obligations := 2, merges := 5 }
-/
#guard_msgs in
#eval mergeSummary (.pathsAbove 2) (deepElse 6)
/--
info: some { finished := 3, stopped := 0, unmatchedExits := 0, obligations := 3, merges := 4 }
-/
#guard_msgs in
#eval mergeSummary (.pathsAbove 3) (deepElse 6)
-- Two nested ifs (`nested`, three ways through): under `pathsAbove 2` the inner join merges,
-- since the outer fork's else-branch is still pending on the worklist, so three paths would
-- exist.
/--
info: some { finished := 2, stopped := 0, unmatchedExits := 0, obligations := 2, merges := 1 }
-/
#guard_msgs in
#eval mergeSummary (.pathsAbove 2) nested
/-- A join view with `pending` pending paths. -/
private def view (pending : Nat) : JoinView :=
  { proc := "", depth := 0, pending := pending, finished := 0, differing := Thunk.pure 0 }
#guard ((MergeMode.ofString? "merge-above:3").map fun m => (MergePolicy.ofMode m (view 1),
  MergePolicy.ofMode m (view 4))) == some (false, true)
#guard (MergeMode.ofString? "per-path").map (MergePolicy.ofMode · (view 0)) == some false
#guard (MergeMode.ofString? "merged").map (MergePolicy.ofMode · (view 0)) == some true
#guard (MergeMode.ofString? "sometimes").isNone && (MergeMode.ofString? "merge-above:").isNone
-- A bound of 0 is refused, as for `--path-cap`.
#guard (MergeMode.ofString? "merge-above:0").isNone &&
  MergeMode.ofString? "merge-above:1" == some (.pathsAbove 1)
-- Only the spellings above name a mode.
#guard ["never", "always", "paths:2", "pathsAbove:2"].all (MergeMode.ofString? · |>.isNone)

-- A custom policy given to the phase (`toSymExecObligationProgram`'s `policy`) replaces the
-- preset `symExec` names: one that always merges gives what `.always` gives.
private def threeSeqPgm : StrataDDM.Program :=
#strata
program Core;
procedure P(x : int, out r : int) {
  if (int.gt(x, 0)) { r := 1; } else { r := 2; }
  if (int.gt(x, 5)) { r := int.add(r, 1); }
  if (int.gt(x, 9)) { r := int.add(r, 1); }
  assert [a]: int.gt(r, 0);
};
#end
/-- The obligation program `toSymExecObligationProgram` builds for `pgm` under merge mode `mode`
    and `policy`, with its path, obligation and merge counts. -/
private def phaseRun (pgm : StrataDDM.Program) (mode : MergeMode)
    (policy : Option MergePolicy := none) : String :=
  match (progOf pgm).map (toSymExecObligationProgram
      { VerifyOptions.default with verbose := .quiet, symExec := some mode }
      · (policy := policy)) with
  | none => "error: type checking failed"
  | some (.error e) => s!"error: {e.message}"
  | some (.ok (p, st)) =>
    s!"paths {st.get "SymExec.paths"}, obligations {st.get "SymExec.obligations"}, " ++
      s!"merges {st.get "SymExec.merges"}\n{Std.format p}"
/-- info: "paths 8, obligations 8, merges 0" -/
#guard_msgs in
#eval ((phaseRun threeSeqPgm .never).splitOn "\n").headD ""
/-- info: "paths 1, obligations 1, merges 3" -/
#guard_msgs in
#eval ((phaseRun threeSeqPgm .never (some fun _ => true)).splitOn "\n").headD ""
#guard phaseRun threeSeqPgm .never (some fun _ => true) == phaseRun threeSeqPgm .always
-- A policy that merges only while another path is pending.
/-- info: "paths 4, obligations 4, merges 3" -/
#guard_msgs in
#eval ((phaseRun threeSeqPgm .never (some fun v => v.pending > 0)).splitOn "\n").headD ""
-- With merging, extraction from `treeStmts` yields the obligations recorded on the paths (same
-- set and count).
#guard [twoSeq, threeSeq, branchAssume, early, nested, failing, nestedExit].all
  (sameAsPaths · .always)

/-! ## Replaying per-path counterexamples -/


-- `failing`: the then-path (x > 0, r := 0) breaks `r > 0`. A model with x = 3 is a real run
-- that fails it; x = -1 takes the else-path, where the assert holds.
#guard replayAt failing .never 0 [("x_0", 3)] == some .genuine
#guard replayAt failing .never 0 [("x_0", -1)] == some .spurious
-- A value of a variable declared without one comes from the model (symbol `b_2`, named after
-- the variable): b = -5 breaks `b > 0`, b = 5 does not.
private def havocAssert := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  var b : int;
  assert [hb]: int.gt(b, 0);
};
#end
#guard replayAt havocAssert .never 0 [("b_2", -5)] == some .genuine
#guard replayAt havocAssert .never 0 [("b_2", 5)] == some .spurious
-- x = 2 satisfies the precondition and breaks `x > 5`; x = -3 violates the precondition, so
-- replay cannot validate it.
private def preFails := procOf <|
#strata
program Core;
procedure P(x : int, out r : int)
spec { requires [pre]: int.gt(x, 0); }
{
  assert [a5]: int.gt(x, 5);
};
#end
#guard replayAt preFails .never 0 [("x_0", 2)] == some .genuine
#guard replayAt preFails .never 0 [("x_0", -3)] ==
  some (.cantValidate (.assumptionFalseUnderReplay "pre"))
-- An obligation on a merged path is replayed: the model picks the run, by the branch each
-- merge's guard takes under it. Merged at its join, `r` is `if x > 0 then 1 else 0`: x = -1
-- takes the else-branch and fails `r > 0`, x = 3 passes it.
private def mergedFailing := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  if (int.gt(x, 0)) { r := 1; } else { r := 0; }
  assert [a]: int.gt(r, 0);
};
#end
#guard ((run mergedFailing .always).map fun r => r.obligations.map (·.merged)) == some [true]
#guard replayAt mergedFailing .always 0 [("x_0", -1)] == some .genuine
#guard replayAt mergedFailing .always 0 [("x_0", 3)] == some .spurious
-- A havoc in each merged branch: the oracle is the chosen branch's symbol (`r_2` for the
-- then-branch, `r_3` for the else-branch); the other branch's symbol is not consumed.
private def havocBoth := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  if (int.gt(x, 0)) { havoc r; } else { havoc r; r := int.neg(r); }
  assert [a]: int.gt(r, 0);
};
#end
/--
info: [a] under [$__joinr_0 == (if int.gt($__symx_0, 0) then $__symr_2 else int.neg($__symr_3))] 
  check: int.gt($__joinr_0, 0)
-/
#guard_msgs (whitespace := lax) in
#eval printObls (run havocBoth .always)
#guard replayAt havocBoth .always 0 [("x_0", 3), ("r_2", -1), ("r_3", -1)] == some .genuine
#guard replayAt havocBoth .always 0 [("x_0", 3), ("r_2", 5), ("r_3", 5)] == some .spurious
#guard replayAt havocBoth .always 0 [("x_0", -1), ("r_2", -1), ("r_3", 5)] == some .genuine
#guard replayAt havocBoth .always 0 [("x_0", -1), ("r_2", 5), ("r_3", -5)] == some .spurious
-- Nested merges: the inner merge's choices sit inside the outer then-branch's.
private def havocNested := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  if (int.gt(x, 0)) {
    if (int.gt(x, 5)) { havoc r; } else { r := 0; }
  } else { havoc r; }
  assert [a]: int.gt(r, 0);
};
#end
/--
info: [a] under [$__joinr_0 == (if int.gt($__symx_0, 5) then $__symr_2 else 0), $__joinr_1 == (if int.gt($__symx_0, 0) then $__joinr_0 else $__symr_3)]  check: int.gt($__joinr_1, 0)
-/
#guard_msgs (whitespace := lax) in
#eval printObls (run havocNested .always)
#guard ((run havocNested .always).map (·.merges)) == some 2
#guard replayAt havocNested .always 0 [("x_0", 7), ("r_2", -2), ("r_3", 9)] == some .genuine
#guard replayAt havocNested .always 0 [("x_0", 7), ("r_2", 4), ("r_3", -9)] == some .spurious
#guard replayAt havocNested .always 0 [("x_0", 3), ("r_2", 4), ("r_3", 9)] == some .genuine
#guard replayAt havocNested .always 0 [("x_0", -1), ("r_2", -2), ("r_3", 9)] == some .spurious
-- A guard that does not evaluate to a Boolean under the model (here the model gives the
-- Boolean input an integer): no replay.
private def havocOnBool := procOf <|
#strata
program Core;
procedure P(c : bool, out r : int) {
  if (c) { havoc r; } else { havoc r; }
  assert [a]: int.gt(r, 0);
};
#end
#guard replayAt havocOnBool .always 0 [("c_0", 1), ("r_2", 1), ("r_3", 1)] == none

/-! ## Completeness and the path limit -/

/-- info: some (Core.SymExec.Completeness.complete) -/
#guard_msgs in
#eval (run threeSeq).map (·.completeness)
/-- info: some (Core.SymExec.Completeness.complete) -/
#guard_msgs in
#eval (run threeSeq (cfg := { maxPaths := some 8 })).map (·.completeness)
/-- info: some (Core.SymExec.Completeness.notAnalyzed ["the path limit was reached"]) -/
#guard_msgs in
#eval (run threeSeq (cfg := { maxPaths := some 3 })).map (·.completeness)
-- Paths still pending at the limit are not explored: they record no obligation. Here the
-- limit is reached right after the second fork, with four paths pending and none finished.
/-- info: some (0, 4, 0) -/
#guard_msgs in
#eval (run threeSeq (cfg := { maxPaths := some 3 })).map fun r =>
  (r.finished, r.countStatus (· matches .overPathLimit), r.obligations.length)
-- A stopped path, an exhausted work bound and an unmatched exit make a run incomplete.
/--
info: some (Core.SymExec.Completeness.notAnalyzed ["a path stopped: run interrupted: call (eliminate
  calls first)"])
-/
#guard_msgs (whitespace := lax) in
#eval (run (procOf callPgm)).map (·.completeness)
/-- info: some (Core.SymExec.Completeness.notAnalyzed ["the work bound ran out"]) -/
#guard_msgs in
#eval ((twoBranches.map (exploreProc {} 3 1000 Core.Factory ·)).map (·.completeness))
/--
info: some (Core.SymExec.Completeness.notAnalyzed ["a path exited to unmatched label 'nowhere'"])
-/
#guard_msgs in
#eval (run unmatched).map (·.completeness)

/-! ## Naming merged values at joins (`nameJoinValues`) -/

/-- The join symbols the first obligation of `r` defines, each with its type, oldest first. -/
private def joinDefs (r : Option Result) : Option (List String) :=
  r.bind fun r => r.obligations.head?.map fun o =>
    (o.pc.reverse.filterMap fun (l, e) =>
      if l.startsWith "<join_value:" then
        match e with
        | .eq _ (.fvar _ s (some ty)) _ => some s!"{s.name} : {Std.format ty}"
        | _ => some s!"unexpected: {Std.format e}"
      else none)

-- Merged values of every kind of type get a join symbol of their variable's declared type: a
-- primitive, a map through a type synonym, a datatype, an opaque type, and a polymorphic
-- function's result. None is left unnamed.
private def joinTypes := procOf <|
#strata
program Core;
type T;
type IM := Map int int;
datatype IntList { Nil(), Cons(hd: int, tl: IntList) };
function idf<a>(y : a) : a { y }
procedure P(x : int, t1 : T, t2 : T, out r : int) {
  var b : bool;
  var m : IM;
  var l : IntList;
  var t : T;
  if (int.gt(x, 0)) {
    r := 1; b := true; m := m[0 := 1]; l := Cons(1, Nil()); t := t1;
  } else {
    r := idf(x); b := false; m := m[0 := 2]; l := Nil(); t := t2;
  }
  assert [a]: int.gt(r, 0);
};
#end
/--
info: some ["$__joinb_0 : bool", "$__joinl_1 : IntList", "$__joinm_2 : (Map int int)",
  "$__joinr_3 : int", "$__joint_4 : T"]
-/
#guard_msgs (whitespace := lax) in
#eval joinDefs (run joinTypes .always)
#guard ((run joinTypes .always).map (·.joinValuesUnnamed)) == some 0
#guard ((run joinTypes .always).map (·.merges)) == some 1

-- Two variables merged to the same value share one join symbol, so `r == y` folds to `true`.
private def sharedValue := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  var y : int;
  if (int.gt(x, 0)) { r := 1; y := 1; } else { r := 2; y := 2; }
  assert [same]: r == y;
};
#end
/-- info: some ["$__joinr_0 : int"] -/
#guard_msgs in
#eval joinDefs (run sharedValue .always)
/-- info: [same] under [$__joinr_0 == (if int.gt($__symx_0, 0) then 1 else 2)]  check: true -/
#guard_msgs in
#eval printObls (run sharedValue .always)

-- A function-typed value is never named, and an untyped one is left unnamed and counted
-- (`nameJoinStep`; the explorer records every declared type, so the count stays 0 in a run).
private def stepOn (ta tb : Std.TreeMap CoreIdent LMonoTy identCmp) :
    Nat × Nat × Nat :=
  letI := symLang ({} : ExploreCfg)
  let x : CoreIdent := ⟨"f", ()⟩
  let v := LExpr.ite symExecLoc (mkSym defaultSymPrefix 0 .bool "c")
    (mkSym defaultSymPrefix 1 (.arrow .int .int) "g")
    (mkSym defaultSymPrefix 2 (.arrow .int .int) "h")
  let r := nameJoinStep (scfg := {}) ta tb (IStore.ofStore (fun _ => none), [], 0, 0, []) (x, v)
  (r.2.1.length, r.2.2.1, r.2.2.2.1)
private def tyMap (ty : Option LMonoTy) : Std.TreeMap CoreIdent LMonoTy identCmp :=
  match ty with
  | some ty => ({} : Std.TreeMap CoreIdent LMonoTy identCmp).insert ⟨"f", ()⟩ ty
  | none => {}
-- (definitions added, join counter, values left unnamed)
#guard stepOn (tyMap (some (.arrow .int .int))) (tyMap (some (.arrow .int .int))) == (0, 0, 0)
#guard stepOn (tyMap none) (tyMap none) == (0, 0, 1)
#guard stepOn (tyMap (some .int)) (tyMap (some .bool)) == (0, 0, 1)
#guard stepOn (tyMap (some .int)) (tyMap (some .int)) == (1, 1, 0)
-- A type with a function inside, such as a map to functions, is not named either.
#guard stepOn (tyMap (some (.tcons "Map" [.int, .arrow .int .int])))
  (tyMap (some (.tcons "Map" [.int, .arrow .int .int]))) == (0, 0, 0)
/-- The definitions one naming step adds, as (label, defined symbol). -/
private def stepDefs (ty : LMonoTy) : List (String × String) :=
  letI := symLang ({} : ExploreCfg)
  let x : CoreIdent := ⟨"f", ()⟩
  let v := LExpr.ite symExecLoc (mkSym defaultSymPrefix 0 .bool "c")
    (mkSym defaultSymPrefix 1 ty "g") (mkSym defaultSymPrefix 2 ty "h")
  let r := nameJoinStep (scfg := {}) (tyMap (some ty)) (tyMap (some ty))
    (IStore.ofStore (fun _ => none), [], 0, 0, []) (x, v)
  r.2.1.map fun (l, e) => match e with
    | .eq _ (.fvar _ s _) _ => (l, s.name)
    | _ => (l, "unexpected")
#guard stepDefs .int == [("<join_value: f>", "$__joinf_0")]
-- A value already named at this join by a symbol of another type gets a fresh symbol of its own
-- type (`$__joinf_1`, from counter 1), not the earlier one.
#guard
  letI := symLang ({} : ExploreCfg)
  let x : CoreIdent := ⟨"f", ()⟩
  let v := LExpr.ite symExecLoc (mkSym defaultSymPrefix 0 .bool "c")
    (mkSym defaultSymPrefix 1 .int "g") (mkSym defaultSymPrefix 2 .int "h")
  let r := nameJoinStep (scfg := {}) (tyMap (some .int)) (tyMap (some .int))
    (IStore.ofStore (fun _ => none), [], 1, 0, [(v, mkSym defaultJoinPrefix 0 .bool "y")]) (x, v)
  (r.2.1.map fun (l, e) => match e with
    | .eq _ (.fvar _ s _) _ => (l, s.name)
    | _ => (l, "unexpected")) == [("<join_value: f>", "$__joinf_1")]

-- The tree program declares a join symbol by an `init` at its first definition on the path
-- (`newAssumes`); an entry with another label, one whose left side is not a join symbol, and a
-- later entry of the same form for a symbol already defined stay `assume`s.
private def joinDefFor (s : Expression.Expr) (n : Nat := 1) : Expression.Expr :=
  LExpr.eq symExecLoc s (mkSym defaultSymPrefix n .int "x")

private def stmtShape : Statement → String
  | .cmd (.cmd (.init x (.forAll _ ty) (.det v) _)) =>
    s!"init {x.name} : {Std.format ty} := {Std.format v}"
  | .cmd (.cmd (.assume l e _)) => s!"assume [{l}] {Std.format e}"
  | _ => "another statement"

private def rJoin : Expression.Expr := mkSym "$__join0_" 0 .int "r"

/--
info: init $__join0_r_0 : int := $__symx_1
assume [<join_value: r>] $__join0_r_0 == $__symx_2
assume [a] $__join0_r_0 == $__symx_1
assume [<join_value: r>] $__symr_0 == $__symx_1
-/
#guard_msgs in
#eval IO.println <| "\n".intercalate <| (newAssumes
  [((joinValueLabel ⟨"r", ()⟩), joinDefFor (mkSym defaultSymPrefix 0 .int "r")),
   ("a", joinDefFor rJoin),
   ((joinValueLabel ⟨"r", ()⟩), joinDefFor rJoin 2),
   ((joinValueLabel ⟨"r", ()⟩), joinDefFor rJoin)] 0).map stmtShape

-- At a merge, a branch's join definition is kept as it is and its other entries go under the
-- guard (`mergeOwn`), so the definition of a symbol named before the fork, given here as
-- `defined`, goes under the guard too.
/-- info: [("<join_value: r>", "$__join0_r_0 == $__symx_1"), ("a", "$__symg_9")] -/
#guard_msgs in
#eval (mergeOwn (fun _ => mkSym defaultSymPrefix 9 .bool "g") {}
  [((joinValueLabel ⟨"r", ()⟩), joinDefFor rJoin), ("a", Core.true)]).map
    fun (l, e) => (l, toString (Std.format e))

/-- info: [("<join_value: r>", "$__symg_9"), ("a", "$__symg_9")] -/
#guard_msgs in
#eval (mergeOwn (fun _ => mkSym defaultSymPrefix 9 .bool "g") (Std.HashSet.ofList ["$__join0_r_0"])
  [((joinValueLabel ⟨"r", ()⟩), joinDefFor rJoin), ("a", Core.true)]).map
    fun (l, e) => (l, toString (Std.format e))

-- A merge guard can mention a join symbol. Replay reads a merge's guard when the merged branches
-- made choices (here the havocs), to pick the branch the model's run takes; the second fork's
-- guard is `$__joinr_0 > 1`, so the model must give `$__joinr_0`. Without it, replay cannot
-- validate the model: it does not guess a default.
private def guardOnJoin := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  if (int.gt(x, 0)) { r := 1; } else { r := 2; }
  if (int.gt(r, 1)) { havoc r; } else { havoc r; }
  assert [a]: int.gt(r, 5);
};
#end
/-- A model giving each listed symbol, by its full name, its `int` value. -/
private def fullModel (bs : List (String × Int)) : CoreIdent → Option Expression.Expr := fun x =>
  (bs.find? fun (n, _) => x.name == n).map fun (_, v) => .intConst valueLoc v
private def replayFull (p : Option Procedure) (bs : List (String × Int)) :
    Option (CEValidationVerdict StopReason) :=
  (run p .always).bind fun r => r.obligations[0]? >>= fun o =>
    replayObl Core.Factory r o (fullModel bs)
/--
info: [a] under [$__joinr_0 == (if int.gt($__symx_0, 0) then 1 else 2), $__joinr_1 == (if
  int.gt($__joinr_0, 1) then $__symr_2 else $__symr_3)]  check: int.gt($__joinr_1, 5)
-/
#guard_msgs (whitespace := lax) in
#eval printObls (run guardOnJoin .always)
-- `x = -1`: `r` is 2 after the first join, so the run takes the first havoc (`r_2`).
#guard replayFull guardOnJoin
  [("$__symx_0", -1), ("$__joinr_0", 2), ("$__symr_2", 9), ("$__symr_3", 0)] == some .spurious
#guard replayFull guardOnJoin
  [("$__symx_0", -1), ("$__joinr_0", 2), ("$__symr_2", 0), ("$__symr_3", 9)] == some .genuine
#guard replayFull guardOnJoin [("$__symx_0", -1), ("$__symr_2", 9), ("$__symr_3", 0)] == none

/-! ## Ending infeasible paths -/

/-- How each path of `r` ended that did not finish or fork, in node order. -/
private def endsOf (r : Option Result) : Option (List String) :=
  r.map fun r => r.nodes.toList.filterMap fun n => match n.status with
    | .infeasible l => some s!"infeasible {l}"
    | .stopped reason => some s!"stopped: {reason}"
    | _ => none

-- A failed assert does not end its path: the later check gets an obligation too.
private def failThenCheck := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  assert [f]: false;
  assert [later]: int.gt(x, 0);
};
#end
#guard ((run failThenCheck).map fun r => r.obligations.map (·.label)) == some ["f", "later"]
#guard endsOf (run failThenCheck) == some []
-- An assume that contradicts the path condition without being literal `false` does not end the
-- path: the check after it gets an obligation, under both conditions, for the solver.
private def contraAssume := procOf <|
#strata
program Core;
procedure P(x : int, out r : int) {
  if (int.gt(x, 0)) { r := 1; } else {
    assume [no]: int.gt(x, 0);
    assert [a]: int.gt(x, 7);
  }
};
#end
#guard ((run contraAssume).map fun r => r.obligations.map (·.label)) == some ["a"]
/-- info: some [] -/
#guard_msgs in
#eval endsOf (run contraAssume)
#guard ((run contraAssume).map (·.completeness)) == some .complete
/-- info: some (1, 1, []) -/
#guard_msgs in
#eval (run contraAssume .always).map (fun r => (r.merges, r.obligations.length, unreachedLabels r))
-- An assume of literal `false` ends the path too.
#guard ((run assumeFalse).map fun r => (r.obligations.length,
  r.countStatus (· matches .infeasible _))) == some (0, 1)

/-! ## Many paths and checks -/

-- Eight symbolic `if`s, each followed by an assert, then twenty asserts and a second assert
-- labelled `t0`: 256 paths, each reaching all 29 checks. The checks are told apart by label and
-- metadata, so the two `t0` asserts are two checks. The assert in the `if (false)` branch is the
-- one check no path reaches.
private def manyChecks := procOf <|
#strata
program Core;
procedure P(x : int, b0 : bool, b1 : bool, b2 : bool, b3 : bool,
    b4 : bool, b5 : bool, b6 : bool, b7 : bool, out r : int) {
  r := x;
  if (false) { assert [never]: int.gt(r, x); }
  if (b0) { r := int.add(r, 1); } else { r := int.sub(r, 1); }
  assert [s0]: int.ge(r, int.sub(x, 100));
  if (b1) { r := int.add(r, 2); } else { r := int.sub(r, 1); }
  assert [s1]: int.ge(r, int.sub(x, 100));
  if (b2) { r := int.add(r, 3); } else { r := int.sub(r, 1); }
  assert [s2]: int.ge(r, int.sub(x, 100));
  if (b3) { r := int.add(r, 4); } else { r := int.sub(r, 1); }
  assert [s3]: int.ge(r, int.sub(x, 100));
  if (b4) { r := int.add(r, 5); } else { r := int.sub(r, 1); }
  assert [s4]: int.ge(r, int.sub(x, 100));
  if (b5) { r := int.add(r, 6); } else { r := int.sub(r, 1); }
  assert [s5]: int.ge(r, int.sub(x, 100));
  if (b6) { r := int.add(r, 7); } else { r := int.sub(r, 1); }
  assert [s6]: int.ge(r, int.sub(x, 100));
  if (b7) { r := int.add(r, 8); } else { r := int.sub(r, 1); }
  assert [s7]: int.ge(r, int.sub(x, 100));
  assert [t0]: int.ge(int.add(r, 0), int.sub(x, 1000));
  assert [t1]: int.ge(int.add(r, 1), int.sub(x, 1000));
  assert [t2]: int.ge(int.add(r, 2), int.sub(x, 1000));
  assert [t3]: int.ge(int.add(r, 3), int.sub(x, 1000));
  assert [t4]: int.ge(int.add(r, 4), int.sub(x, 1000));
  assert [t5]: int.ge(int.add(r, 5), int.sub(x, 1000));
  assert [t6]: int.ge(int.add(r, 6), int.sub(x, 1000));
  assert [t7]: int.ge(int.add(r, 7), int.sub(x, 1000));
  assert [t8]: int.ge(int.add(r, 8), int.sub(x, 1000));
  assert [t9]: int.ge(int.add(r, 9), int.sub(x, 1000));
  assert [t10]: int.ge(int.add(r, 10), int.sub(x, 1000));
  assert [t11]: int.ge(int.add(r, 11), int.sub(x, 1000));
  assert [t12]: int.ge(int.add(r, 12), int.sub(x, 1000));
  assert [t13]: int.ge(int.add(r, 13), int.sub(x, 1000));
  assert [t14]: int.ge(int.add(r, 14), int.sub(x, 1000));
  assert [t15]: int.ge(int.add(r, 15), int.sub(x, 1000));
  assert [t16]: int.ge(int.add(r, 16), int.sub(x, 1000));
  assert [t17]: int.ge(int.add(r, 17), int.sub(x, 1000));
  assert [t18]: int.ge(int.add(r, 18), int.sub(x, 1000));
  assert [t19]: int.ge(int.add(r, 19), int.sub(x, 1000));
  assert [t0]: int.ge(r, int.sub(x, 2000));
};
#end
-- Paths finished, obligations, checks reached, distinct labels among them, and the labels of
-- the checks no path reached.
/-- info: some (256, 5886, 29, 28, ["never"]) -/
#guard_msgs in
#eval (manyChecks.map (exploreProc {} 1000000 1000 Core.Factory ·)).map fun r =>
  (r.finished, r.obligations.length, r.reached.fold (fun n _ mds => n + mds.size) 0,
    r.reached.size, r.unreached.map (·.label))

/-! ## Merging needs the path conditions the engine builds

A merge is correct only if, at the join, the then-branch's path condition is the fork's path
condition plus the guard (and whatever the branch assumed after it), and the else-branch's is the
fork's path condition plus the negated guard (and the same). The engine always builds them that
way, so no Core program can break it. To test that the explorer refuses to merge when they are
built differently, each test below replaces the engine's step by one that tampers with the path
condition, and runs `twoBranches`:

```
if (x > 0) { r := 1 } else { r := 2 }; assert r > 0
```

Each run reports (paths finished, merges): `(1, 1)` means the two branches merged into one path,
`(2, 0)` that they stayed apart. -/

/-- The engine's step, except that at the fork each side's path condition gets a second new fact,
    `extra: true`, on top of the guard. -/
private def extraAtFork : ProcBodyShape {} (StmtConfig {}) :=
  { structuredShape {} with
    step := fun fuel c cfg st =>
      let outs := (structuredShape {}).step fuel c cfg st
      if outs.length == 2 then
        outs.map fun (o, st') => (o, { st' with pc := ("extra", Core.true) :: st'.pc })
      else outs }

/-- The engine's step, except that at the fork both sides' oldest fact (the one the fork started
    with) is replaced by `pre: p` (a fresh symbol). Each side still has exactly one new fact, so the lengths
    look right, but the part both share is no longer the fork's path condition. -/
private def tailAtFork : ProcBodyShape {} (StmtConfig {}) :=
  { structuredShape {} with
    step := fun fuel c cfg st =>
      let outs := (structuredShape {}).step fuel c cfg st
      if outs.length == 2 then
        outs.map fun (o, st') => (o, { st' with pc := st'.pc.dropLast ++ [("pre", mkSym "$__s" 9 .bool "p")] })
      else outs }

/-- The engine's step, except that after the fork, on the else-branch only, each step replaces
    the oldest fact by `pre: p` (a fresh symbol). The fork itself looks right, so the join opens; at the join
    the two branches no longer share the fork's facts. -/
private def rewriteBaseOnElse : ProcBodyShape {} (StmtConfig {}) :=
  { structuredShape {} with
    step := fun fuel c cfg st =>
      let outs := (structuredShape {}).step fuel c cfg st
      -- The engine labels the else-branch's entry `<label_ite_cond_false: ...>`
      -- (`forkEffects`, SymExec.lean).
      let onElse := (st.pc.head?.map (·.1.startsWith "<label_ite_cond_false")).getD false
      if onElse then
        outs.map fun (o, st') => (o, { st' with pc := st'.pc.dropLast ++ [("pre", mkSym "$__s" 9 .bool "p")] })
      else outs }

/-- `twoBranches`'s body run by `sh` under the policy `pol` from a store binding `x` and `r` to
    symbols and the path condition `pc`. -/
private def runShapeResult (sh : ProcBodyShape {} (StmtConfig {}))
    (pc : List (String × Expression.Expr) := []) (pol : MergePolicy := .always) : Option Result :=
  letI := symLang {}
  twoBranches.bind fun p => match p.body with
    | .structured ss _ =>
      let σ := (IStore.ofStore (fun _ => none)).update (⟨"x", ()⟩ : CoreIdent)
        (mkSym "$__s" 0 .int "x") |>.update (⟨"r", ()⟩ : CoreIdent) (mkSym "$__s" 1 .int "r")
      let env : IEnv Expression := { store := σ, factory := Core.Factory }
      let start : Entry (StmtConfig {}) :=
        { cfg := .stmts ss env, st := { next := 2, pc }, node := 0, budget := 1000 }
      some (explore sh 10000 start pol)
    | .cfg _ _ | .abstract => none

/-- `runShapeResult`'s paths finished and merges. -/
private def runShape (sh : ProcBodyShape {} (StmtConfig {}))
    (pc : List (String × Expression.Expr) := []) (pol : MergePolicy := .always) :
    Option (Nat × Nat) :=
  (runShapeResult sh pc pol).map fun r => (r.finished, r.merges)

-- The engine's own step merges, starting from no facts and from one fact `pre: true`.
#guard runShape (structuredShape {}) == some (1, 1)
#guard runShape (structuredShape {}) [("pre", Core.true)] == some (1, 1)
-- Two new facts per side at the fork: the explorer opens no join, so no merge.
#guard runShape extraAtFork == some (2, 0)
-- Shared facts changed at the fork: no join opens (`openJoin`), so no merge.
#guard runShape tailAtFork [("pre", Core.true)] == some (2, 0)
-- Shared facts changed later on one branch: the join opens, the merge refuses
-- (`mergeShapeOk`), so the branches stay apart.
#guard runShape rewriteBaseOnElse [("pre", Core.true)] == some (2, 0)

/-! ## A step with no outcome

If a step returns no outcome, the path stops, so the run is reported as not analysed instead of
complete. -/

/-- The engine's step, except that it returns no outcome. -/
private def noOutcome : ProcBodyShape {} (StmtConfig {}) :=
  { structuredShape {} with step := fun _ _ _ _ => [] }

/--
info: some (Core.SymExec.Completeness.notAnalyzed
  ["a path stopped: run interrupted: a step had no outcome"])
-/
#guard_msgs (whitespace := lax) in
#eval (runShapeResult noOutcome).map (·.completeness)

/-! ## A merge policy that reads how many variables differ

The policy is asked before the merge is computed; the number of variables whose values differ
(`JoinView.differing`) is computed only if the policy reads it. In `twoBranches`, one variable,
`r`, differs (1 against 2). -/

-- At most 0 differing variables: no merge.
#guard runShape (structuredShape {}) (pol := fun v => v.differing.get ≤ 0) == some (2, 0)
-- At most 1: merge.
#guard runShape (structuredShape {}) (pol := fun v => v.differing.get ≤ 1) == some (1, 1)

end SymExecTest

end -- meta section
