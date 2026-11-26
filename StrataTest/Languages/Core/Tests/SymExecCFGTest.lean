/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.SymExecTree
meta import Strata.Languages.Core.SymExecReplay
meta import Strata.Languages.Core.Verifier
meta import Strata.Transform.StructuredToUnstructured
meta import Strata.SimpleAPI
meta import StrataTest.Languages.Core.Tests.SymExecTestSupport
import StrataDDM.Integration.Lean.HashCommands

/-! # Symbolic execution of procedures with CFG bodies (`Core.SymExec`)

Each test program is Core source with a `cfg` body, translated and type-checked as the verifier
does before VC generation (`procOf`); a program that fails type checking gives no procedure, so
every check on it fails. The post-dominator analysis (`computePostIdoms`) is checked against
the textbook set-dataflow fixpoint on hand-built graphs.
-/

meta section

namespace SymExecCFGTest

open Core Core.SymExec Lambda Imperative SymExecTestSupport

private abbrev testLoc : ExprSourceLoc := ExprSourceLoc.synthesized "test"

/-- A run's counts: paths finished, paths stopped, obligations, joins merged, unreached
    checks. -/
private structure Summary where
  finished : Nat
  stopped : Nat
  obligations : Nat
  merges : Nat
  unreached : Nat
  deriving Repr

/-- The counts of `run p pol`. -/
private def summary (p : Option Procedure) (pol : MergePolicy := .never) : Option Summary :=
  (run p pol).map fun r =>
    ⟨r.finished, r.stopped, r.obligations.length, r.merges, r.unreached.length⟩

/-- Print the obligations of `run p pol`, or `no result`. -/
private def obls (p : Option Procedure) (pol : MergePolicy := .never) : IO Unit :=
  printObls (run p pol)

/-- The labels and path-condition labels of the unreached checks of `run p pol`. -/
private def unreachedOf (p : Option Procedure) (pol : MergePolicy := .never) :
    Option (List (String × List String)) :=
  (run p pol).map fun r => r.unreached.map fun o => (o.label, o.pc.map (·.1))

/-- A block of a hand-built graph: no commands, `finish` without successors, a jump to one
    successor, a branch on `c` to the first two. -/
private def gb (succs : List String) : DetBlock String Command Expression :=
  { cmds := [],
    transfer := match succs with
      | [] => .finish #[]
      | [a] => .goto a
      | a :: b :: _ => .condGoto (.fvar testLoc ⟨"c", ()⟩ none) a b #[] }

/-- A hand-built graph from each block's label and successors. -/
private def graph (entry : String) (bs : List (String × List String)) : Core.DetCFG :=
  { entry, blocks := bs.map fun (l, s) => (l, gb s) }

/-- Each block's immediate post-dominator (`computePostIdoms`), in block order; blocks with
    none are left out. -/
private def ipdomList (g : Core.DetCFG) : List (String × Option String) :=
  let m := g.computePostIdoms
  g.labels.filterMap fun l => (m.get? l).map (l, ·)

/-- The end node of the reference analysis. -/
private def endNode : String := "<end>"

/-- Reference post-dominator sets: the fixpoint of `pdom(end) = {end}` and
    `pdom(n) = {n} ∪ ⋂ pdom(s)` over the successors `s` of `n` (a `finish` block's successor is
    the end), iterated `n*n+1` times from every set full. -/
private def postDominatorsFullFuel (g : Core.DetCFG) : Std.HashMap String (List String) :=
  Id.run do
  let all := endNode :: g.labels
  let succ (l : String) : List String := match g.blocks.lookup l with
    | some b => match b.transfer with
      | .finish _ => [endNode]
      | t => t.targets
    | none => []
  let mut pdom : Std.HashMap String (List String) := {}
  for l in g.labels do pdom := pdom.insert l all
  pdom := pdom.insert endNode [endNode]
  for _ in List.range (all.length * all.length + 1) do
    for l in g.labels do
      let inter := match succ l with
        | [] => all
        | s :: rest =>
          (pdom.getD s all).filter fun x => rest.all fun t => (pdom.getD t all).contains x
      pdom := pdom.insert l (l :: inter.filter (· != l))
  return pdom

/-- The blocks from which a `finish` block is reachable. -/
private def reachesFinish (g : Core.DetCFG) : List String := Id.run do
  let mut reach : List String := g.blocks.filterMap fun (l, b) =>
    match b.transfer with | .finish _ => some l | _ => none
  for _ in List.range (g.blocks.length + 1) do
    for (l, b) in g.blocks do
      if !reach.contains l && b.transfer.targets.any reach.contains then reach := l :: reach
  return reach

/-- `computePostIdoms` agrees with the reference: it has an entry exactly for the blocks that
    reach a `finish`, and for each the chain of immediate post-dominators up to the end is the
    reference set of post-dominators. -/
private def postIdomsAgree (g : Core.DetCFG) : Bool :=
  let m := g.computePostIdoms
  let ref := postDominatorsFullFuel g
  let reach := reachesFinish g
  let chain (l : String) : List String := Id.run do
    let mut out := [l]
    let mut cur := l
    for _ in List.range (g.blocks.length + 1) do
      match m.get? cur with
      | some (some d) => out := d :: out; cur := d
      | _ => break
    return endNode :: out
  g.labels.all fun l =>
    (m.contains l == reach.contains l) &&
      (!reach.contains l ||
        let c := chain l
        let r := ref.getD l []
        c.all r.contains && r.all c.contains)

/-- One line per result of verifying `pgm` under `--vcgen symexec` with merge policy `merge`
    (`verifyLines`). -/
private def verifyCFG (pgm : StrataDDM.Program) (merge : Core.MergeMode := .never) :
    IO String :=
  verifyLines (Strata.Core.getProgram pgm).1
    { Core.VerifyOptions.default with verbose := .quiet, symExec := some merge }

/-- Print the results of verifying `pgm` under `--vcgen symexec` (`verifyCFG`), first under merge
    policy `never`, then under `always`. -/
private def verifyNeverAlways (pgm : StrataDDM.Program) : IO Unit := do
  IO.println s!"never:\n{← verifyCFG pgm}\nalways:\n{← verifyCFG pgm .always}"

/-! ## Post-dominators -/

/-- A diamond: `E` branches to `A` or `B`, both jump to `J`, which finishes. -/
private def diamondG := graph "E" [("E", ["A", "B"]), ("A", ["J"]), ("B", ["J"]), ("J", [])]
#guard ipdomList diamondG ==
  [("E", some "J"), ("A", some "J"), ("B", some "J"), ("J", none)]
#guard postIdomsAgree diamondG

/-- Nested diamonds: `A` branches again, its arms meet at `K` before `J`. -/
private def nestedG := graph "E"
  [("E", ["A", "B"]), ("A", ["A1", "A2"]), ("A1", ["K"]), ("A2", ["K"]), ("K", ["J"]),
   ("B", ["J"]), ("J", [])]
#guard ipdomList nestedG ==
  [("E", some "J"), ("A", some "K"), ("A1", some "K"), ("A2", some "K"), ("K", some "J"),
   ("B", some "J"), ("J", none)]
#guard postIdomsAgree nestedG

/-- `E` and `A` both branch, and every branch meets at `J`. -/
private def sharedG := graph "E" [("E", ["A", "J"]), ("A", ["B", "J"]), ("B", ["J"]), ("J", [])]
#guard ipdomList sharedG == [("E", some "J"), ("A", some "J"), ("B", some "J"), ("J", none)]
#guard postIdomsAgree sharedG

/-- `A` finishes early, `B` reaches the other `finish` through `J`: the fork at `E` has no
    block on every path to a `finish`. -/
private def earlyG := graph "E" [("E", ["A", "B"]), ("A", []), ("B", ["J"]), ("J", [])]
#guard ipdomList earlyG == [("E", none), ("A", none), ("B", some "J"), ("J", none)]
#guard postIdomsAgree earlyG

/-- `A` jumps to `$__exit`, which is no block (the type checker refuses this; the analysis
    does not rely on it): the end node gets another label, so `A` reaches no `finish` and the
    fork at `E` reaches one only through `B`. -/
private def danglingG := graph "E" [("E", ["A", "B"]), ("A", ["$__exit"]), ("B", [])]
/-- info: [("E", some "B"), ("B", none)] -/
#guard_msgs in
#eval ipdomList danglingG

/-- A loop `H ⇄ L` with exit `X`. -/
private def loopG := graph "E" [("E", ["H"]), ("H", ["L", "X"]), ("L", ["H"]), ("X", [])]
#guard ipdomList loopG == [("E", some "H"), ("H", some "X"), ("L", some "H"), ("X", none)]
#guard postIdomsAgree loopG

/-- `S` cycles forever; `E` branches to it or to `X`; `U` is unreachable. `S` reaches no
    `finish`, so it has no immediate post-dominator; `E` still has `X`. -/
private def stuckG := graph "E"
  [("E", ["S", "X"]), ("S", ["S"]), ("X", []), ("U", ["X"])]
#guard ipdomList stuckG == [("E", some "X"), ("X", none), ("U", some "X")]
#guard postIdomsAgree stuckG

/-- The cycle `A ⇄ B` with two entries (irreducible). -/
private def irreducibleG := graph "E"
  [("E", ["A", "B"]), ("A", ["B"]), ("B", ["A", "X"]), ("X", [])]
#guard ipdomList irreducibleG == [("E", some "B"), ("A", some "B"), ("B", some "X"), ("X", none)]
#guard postIdomsAgree irreducibleG

/-! ## Diamonds and joins -/

-- A diamond: the fork at `entry` joins at `done`, the immediate post-dominator.
private def diamond := procOf <|
#strata
program Core;
procedure P(x : int, out r : int)
cfg entry {
  entry: { branch (int.gt(x, 0)) goto a else goto b; }
  a: { r := 1; goto done; }
  b: { r := 2; goto done; }
  done: { assert [pos]: int.gt(r, 0); return; }
};
#end

/-- info: some { finished := 2, stopped := 0, obligations := 2, merges := 0, unreached := 0 } -/
#guard_msgs in
#eval summary diamond
/-- info: some { finished := 1, stopped := 0, obligations := 1, merges := 1, unreached := 0 } -/
#guard_msgs in
#eval summary diamond .always
/--
info: [pos] under [int.gt($__symx_0, 0)]  check: true
[pos] under [if int.gt($__symx_0, 0) then false else true]  check: true
-/
#guard_msgs in
#eval obls diamond
/--
info: [pos] under [$__joinr_0 == (if int.gt($__symx_0, 0) then 1 else 2)]  check:
  int.gt($__joinr_0, 0)
-/
#guard_msgs (whitespace := lax) in
#eval obls diamond .always
#guard (run diamond).map (·.completeness) == some .complete

-- Nested diamonds: the inner fork joins at `ka`, then the outer one at `done`.
private def nestedDiamond := procOf <|
#strata
program Core;
procedure P(x : int, out r : int)
cfg entry {
  entry: { branch (int.gt(x, 0)) goto a else goto b; }
  a: { branch (int.gt(x, 5)) goto a1 else goto a2; }
  a1: { r := 1; goto ka; }
  a2: { r := 2; goto ka; }
  ka: { goto done; }
  b: { r := 3; goto done; }
  done: { assert [pos]: int.gt(r, 0); return; }
};
#end

/-- info: some { finished := 3, stopped := 0, obligations := 3, merges := 0, unreached := 0 } -/
#guard_msgs in
#eval summary nestedDiamond
/-- info: some { finished := 1, stopped := 0, obligations := 1, merges := 2, unreached := 0 } -/
#guard_msgs in
#eval summary nestedDiamond .always
-- Under `pathsAbove 2` the inner join merges: the outer fork's other branch (`b`) is still
-- pending, so three paths would exist.
/-- info: some { finished := 2, stopped := 0, obligations := 2, merges := 1, unreached := 0 } -/
#guard_msgs in
#eval summary nestedDiamond (.pathsAbove 2)
/--
info: [pos] under [$__joinr_0 == (if int.gt($__symx_0, 5) then 1 else 2), $__joinr_1 == (if int.gt($__symx_0, 0) then $__joinr_0 else 3)]  check: int.gt($__joinr_1, 0)
-/
#guard_msgs (whitespace := lax) in
#eval obls nestedDiamond .always

-- Two forks whose branches all meet at `done`: the inner join and the outer join are the same
-- block, merged innermost first.
private def sharedJoin := procOf <|
#strata
program Core;
procedure P(x : int, out r : int)
cfg entry {
  entry: { r := 0; branch (int.gt(x, 0)) goto a else goto done; }
  a: { branch (int.gt(x, 5)) goto b else goto done; }
  b: { r := 1; goto done; }
  done: { assert [nonneg]: int.ge(r, 0); return; }
};
#end

/-- info: some { finished := 3, stopped := 0, obligations := 3, merges := 0, unreached := 0 } -/
#guard_msgs in
#eval summary sharedJoin
/-- info: some { finished := 1, stopped := 0, obligations := 1, merges := 2, unreached := 0 } -/
#guard_msgs in
#eval summary sharedJoin .always
/--
info: [nonneg] under [$__joinr_0 == (if int.gt($__symx_0, 5) then 1 else 0), $__joinr_1 == (if int.gt($__symx_0, 0) then $__joinr_0 else 0)]  check: int.ge($__joinr_1, 0)
-/
#guard_msgs (whitespace := lax) in
#eval obls sharedJoin .always

-- `pathsAbove 2` merges at a join whenever more than two paths would exist: at the inner join
-- the outer fork's other branch also waits at `done`, so the inner branches merge, and the outer
-- join, where only its two branches remain, keeps them apart.
/-- info: some { finished := 2, stopped := 0, obligations := 2, merges := 1, unreached := 0 } -/
#guard_msgs in
#eval summary sharedJoin (.pathsAbove 2)

-- An early `return`: the branch through `a` finishes before `done`, so the fork's branches meet
-- only at the end of the procedure, where the postcondition is checked.
private def earlyFinish := procOf <|
#strata
program Core;
procedure P(x : int, out r : int)
spec { ensures [post]: int.gt(r, 0); }
cfg entry {
  entry: { branch (int.gt(x, 0)) goto a else goto b; }
  a: { r := 1; return; }
  b: { r := 2; goto done; }
  done: { assert [two]: r == 2; return; }
};
#end

/-- info: some { finished := 2, stopped := 0, obligations := 3, merges := 0, unreached := 0 } -/
#guard_msgs in
#eval summary earlyFinish
/-- info: some { finished := 1, stopped := 0, obligations := 2, merges := 1, unreached := 0 } -/
#guard_msgs in
#eval summary earlyFinish .always
/--
info: [two] under [if int.gt($__symx_0, 0) then false else true]  check: true
[post] under [$__joinr_0 == (if int.gt($__symx_0, 0) then 1 else 2)]  check: int.gt($__joinr_0, 0)
-/
#guard_msgs (whitespace := lax) in
#eval obls earlyFinish .always

-- A guard the path condition decides: the precondition assumes `x > 0`, so the branch takes
-- `a` only. No path visits `b`; its assert is reported as unreached.
private def decided := procOf <|
#strata
program Core;
procedure P(x : int, out r : int)
spec { requires [xpos]: int.gt(x, 0); }
cfg entry {
  entry: { branch (int.gt(x, 0)) goto a else goto b; }
  a: { r := 1; goto done; }
  b: { assert [never]: int.lt(x, 0); r := 2; goto done; }
  done: { assert [pos]: int.gt(r, 0); return; }
};
#end

/-- info: some { finished := 1, stopped := 0, obligations := 1, merges := 0, unreached := 1 } -/
#guard_msgs in
#eval summary decided
#guard unreachedOf decided == some [("never", ["<unreachable_block: b>"])]

-- A local declared in one branch: the paths reach `done` with different variables (`t` only on
-- the path through `a`) and still merge, because `a` does not dominate `done`: `t` is out of
-- scope there (the CFG type checker forbids reading it), so the merge leaves it out.
private def branchLocal := procOf <|
#strata
program Core;
procedure P(x : int, out r : int)
cfg entry {
  entry: { branch (int.gt(x, 0)) goto a else goto b; }
  a: { var t : int := 5; r := t; goto done; }
  b: { r := 2; goto done; }
  done: { assert [pos]: int.gt(r, 0); return; }
};
#end

/-- info: some { finished := 1, stopped := 0, obligations := 1, merges := 1, unreached := 0 } -/
#guard_msgs in
#eval summary branchLocal .always
-- `r` is named by its declared type; nothing is left unnamed.
#guard ((run branchLocal .always).map (·.joinValuesUnnamed)) == some 0
/--
info: [pos] under [$__joinr_0 == (if int.gt($__symx_0, 0) then 5 else 2)]  check:
  int.gt($__joinr_0, 0)
-/
#guard_msgs (whitespace := lax) in
#eval obls branchLocal .always

-- One local declared in two blocks, `d1` and `d2`, neither of which dominates the other. `d1`
-- dominates `j`, so `t` is still in scope at `j` and the merge there keeps it, though `d2` does
-- not dominate `j`. Under `.always` (merged) the run finishes and `t`'s value reaches the `assert`.
private def twoDecls := procOf <|
#strata
program Core;
procedure P(x : int, out r : int)
cfg entry {
  entry: { branch (int.gt(x, 0)) goto d1 else goto d2; }
  d1: { var t : int := 1; branch (int.gt(x, 5)) goto a else goto b; }
  d2: { var t : int := 1; r := 0; return; }
  a: { r := 1; goto j; }
  b: { r := 2; goto j; }
  j: { assert [tpos]: int.gt(t, 0); return; }
};
#end

/-- info: some { finished := 3, stopped := 0, obligations := 2, merges := 0, unreached := 0 } -/
#guard_msgs in
#eval summary twoDecls
/-- info: some { finished := 1, stopped := 0, obligations := 1, merges := 2, unreached := 0 } -/
#guard_msgs in
#eval summary twoDecls .always
/--
info: [tpos] under [int.gt($__symx_0, 0), $__joinr_0 == (if int.gt($__symx_0, 5) then 1 else 2)] 
  check: true
-/
#guard_msgs (whitespace := lax) in
#eval obls twoDecls .always

/-! ## A loop runs out of budget -/

-- `y` counts up to `n`: each pass round the loop forks at `loop`, one path leaving and one
-- staying. Paths that run out of the per-path budget (the one still in the loop, and one that
-- left it too late to finish) stop, so the run is not complete.
private def countUp := procOf <|
#strata
program Core;
procedure P(n : int, out y : int)
spec { requires [nneg]: int.ge(n, 0); ensures [eq]: y == n; }
cfg entry {
  entry: { y := 0; goto loop; }
  loop: { branch (int.lt(y, n)) goto body else goto done; }
  body: { y := int.add(y, 1); goto loop; }
  done: { return; }
};
#end

/--
info: some (6, 2, Core.SymExec.Completeness.notAnalyzed ["a path stopped: replay fuel was
  exhausted"])
-/
#guard_msgs (whitespace := lax) in
#eval (run countUp (fuel := 40)).map fun r => (r.finished, r.stopped, r.completeness)

-- With a constant bound every guard is decided, so the loop never forks: the one path goes
-- round five times and leaves, and the run is complete.
private def countToFive := procOf <|
#strata
program Core;
procedure P(out y : int)
spec { ensures [eq]: y == 5; }
cfg entry {
  entry: { y := 0; goto loop; }
  loop: { branch (int.lt(y, 5)) goto body else goto done; }
  body: { y := int.add(y, 1); goto loop; }
  done: { return; }
};
#end

/-- info: some (1, 0, Core.SymExec.Completeness.complete) -/
#guard_msgs in
#eval (run countToFive).map fun r => (r.finished, r.stopped, r.completeness)
/-- info: [eq] under []  check: true -/
#guard_msgs in
#eval obls countToFive

/-! ## The path limit -/

/-- `p` run under merge policy `pol` with path limit `n`: paths finished, paths over the limit,
    completeness. -/
private def limited (n : Nat) (p : Option Procedure) (pol : MergePolicy := .never) :=
  (run p pol { maxPaths := some n }).map fun r =>
    (r.finished, r.countStatus (· matches .overPathLimit), r.completeness)

-- Three diamonds in a row: 8 ways through. Under a path limit of 4 (`ExploreCfg.maxPaths`) the
-- run stops and the procedure is not analyzed; merging at every join stays under it.
private def threeDiamonds := procOf <|
#strata
program Core;
procedure P(x : int, out r : int)
cfg entry {
  entry: { r := 0; branch (int.gt(x, 0)) goto a1 else goto j1; }
  a1: { r := int.add(r, 1); goto j1; }
  j1: { branch (int.gt(x, 5)) goto a2 else goto j2; }
  a2: { r := int.add(r, 1); goto j2; }
  j2: { branch (int.gt(x, 9)) goto a3 else goto done; }
  a3: { r := int.add(r, 1); goto done; }
  done: { assert [nonneg]: int.ge(r, 0); return; }
};
#end

/--
info: some (2, 3, Core.SymExec.Completeness.notAnalyzed ["the path limit was reached"])
-/
#guard_msgs in
#eval limited 4 threeDiamonds
/-- info: some (1, 0, Core.SymExec.Completeness.complete) -/
#guard_msgs in
#eval limited 4 threeDiamonds .always

/-! ## Many joins -/

/-- `k` diamonds in a row, built as a syntax tree: block `e{i}` branches on `x > i` to `a{i}`
    or `e{i+1}`; `a{i}` declares the local `t{i} := 1`, adds it to `r` and goes to `e{i+1}`;
    `e{k}` finishes. -/
private def diamondChain (k : Nat) : Option Procedure :=
  let id (n : String) : CoreIdent := ⟨n, ()⟩
  let v (n : String) : Expression.Expr := .fvar testLoc (id n) (some .int)
  let int (n : Int) : Expression.Expr := .intConst testLoc n
  let blk (cmds : List Command) (t : DetTransferCmd String Expression) :
      DetBlock String Command Expression := { cmds, transfer := t }
  let blocks := (List.range k).flatMap fun (i : Nat) =>
    [(s!"e{i}", blk [] (.condGoto (.app testLoc (.app testLoc intGtOp (v "x")) (int i)) s!"a{i}"
        s!"e{i+1}" #[])),
     (s!"a{i}", blk [.cmd (.init (id s!"t{i}") (.forAll [] .int) (.det (int 1)) #[]),
                     .cmd (.set (id "r") (.det (.app testLoc (.app testLoc intAddOp (v "r"))
                       (v s!"t{i}"))) #[])] (.goto s!"e{i+1}"))]
  some { header := { name := id "P", typeArgs := [], inputs := [(id "x", .int)],
                     outputs := [(id "r", .int)] }
         spec := { preconditions := [], postconditions := [] }
         body := .cfg { entry := "e0", blocks := blocks ++ [(s!"e{k}", blk [] (.finish #[]))] }
             false }

/-- A body whose only block jumps to `$__symexec_exit`, which is no block (the type checker
    refuses this). The explorer wraps a CFG body in a new entry and exit block whose labels are
    neither labels nor jump targets of the body, so the jump is not taken as one to the
    wrapper's exit: the path stops instead of finishing. -/
private def danglingExit : Option Procedure :=
  some { header := { name := ⟨"P", ()⟩, typeArgs := [], inputs := [], outputs := [] }
         spec := { preconditions := [], postconditions := [] }
         body := .cfg { entry := "s",
                        blocks := [("s", { cmds := [], transfer := .goto "$__symexec_exit" })] }
                            false }

/-- info: some { finished := 0, stopped := 1, obligations := 0, merges := 0, unreached := 0 } -/
#guard_msgs in
#eval summary danglingExit

/-- A body whose entry label, `$__symexec_exit`, is no block. The wrapper's entry jumps to the
    body's entry, so the wrapper's labels avoid that label too: the jump is not taken as one to
    the wrapper's exit, and the path stops instead of finishing without running the body. -/
private def danglingEntry : Option Procedure :=
  some { header := { name := ⟨"P", ()⟩, typeArgs := [], inputs := [], outputs := [] }
         spec := { preconditions := [], postconditions := [] }
         body := .cfg { entry := "$__symexec_exit",
                        blocks := [("s", { cmds := [], transfer := .finish #[] })] } false }

/-- info: some { finished := 0, stopped := 1, obligations := 0, merges := 0, unreached := 0 } -/
#guard_msgs in
#eval summary danglingEntry

/-- Like `danglingEntry`, with the entry label `$__symexec_entry`: the wrapper's own entry does
    not take that label, so it does not jump to itself (which would run until the step budget is
    spent); the path stops at the missing block. -/
private def danglingSelfEntry : Option Procedure :=
  some { header := { name := ⟨"P", ()⟩, typeArgs := [], inputs := [], outputs := [] }
         spec := { preconditions := [], postconditions := [] }
         body := .cfg { entry := "$__symexec_entry",
                        blocks := [("s", { cmds := [], transfer := .finish #[] })] } false }

/--
info: some (Core.SymExec.Completeness.notAnalyzed ["a path stopped: CFG: missing block label"])
-/
#guard_msgs in
#eval (run danglingSelfEntry).map (·.completeness)

-- Merging at each of 200 joins in a row: one path, complete.
/-- info: some (1, 200, Core.SymExec.Completeness.complete) -/
#guard_msgs in
#eval (run (diamondChain 200) .always (fuel := 10000)).map fun r =>
  (r.finished, r.merges, r.completeness)

/-! ## Failed checks and infeasible paths -/

-- Block `c` is reached only past a failed assert.
private def failThenCover := procOf <|
#strata
program Core;
procedure P(x : int, out r : int)
cfg entry {
  entry: { assert [f]: false; goto c; }
  c: { cover [cv]: int.gt(x, 0); r := 1; return; }
};
#end

-- The path continues past the failed assert, and the cover gets an obligation.
#guard ((run failThenCover).map fun r =>
  (r.obligations.map (·.label), r.unreached.map (·.label))) == some (["f", "cv"], [])

-- Block `c` is reached only past an infeasible assume.
private def deadThenCover := procOf <|
#strata
program Core;
procedure P(x : int, out r : int)
cfg entry {
  entry: { assume [no]: false; goto c; }
  c: { cover [cv]: int.gt(x, 0); r := 1; return; }
};
#end

-- The path ends at the assume, so the cover gets no obligation; the run is complete, and the
-- cover is left for `Result.addUnreached` to report.
#guard ((run deadThenCover).map fun r =>
  (r.obligations.map (·.label), r.countStatus (· matches .infeasible _), r.completeness)) ==
  some ([], 1, .complete)
#guard ((run deadThenCover).map fun r => r.unreached.map (·.label)) == some ["cv"]

/-! ## Replaying counterexamples on CFG paths -/

-- `sharedJoin` with `r > 0` asserted at `done`: it fails on the paths that skip `b`.
private def sharedFail := procOf <|
#strata
program Core;
procedure P(x : int, out r : int)
cfg entry {
  entry: { r := 0; branch (int.gt(x, 0)) goto a else goto done; }
  a: { branch (int.gt(x, 5)) goto b else goto done; }
  b: { r := 1; goto done; }
  done: { assert [pos]: int.gt(r, 0); return; }
};
#end

-- Per path: the first obligation is on the path with x ≤ 0 (`r` stays 0), the second on the
-- path through `b`, the third on 0 < x ≤ 5. Replaying the first with x = 7 runs the path
-- through `b`, which passes the check (spurious); replaying the third with x = -1 runs the path
-- with x ≤ 0, which fails it (genuine).
/--
info: [pos] under [if int.gt($__symx_0, 0) then false else true]  check: false
[pos] under [int.gt($__symx_0, 0), int.gt($__symx_0, 5)]  check: true
[pos] under [int.gt($__symx_0, 0), if int.gt($__symx_0, 5) then false else true]  check: false
-/
#guard_msgs in
#eval obls sharedFail
#guard replayAt sharedFail .never 0 [("x_0", 7)] == some .spurious
#guard replayAt sharedFail .never 2 [("x_0", -1)] == some .genuine
-- On the merged path the model picks the run: x = 3 fails the check, x = 7 passes it.
#guard replayAt sharedFail .always 0 [("x_0", 3)] == some .genuine
#guard replayAt sharedFail .always 0 [("x_0", 7)] == some .spurious

/-! ## `verify --vcgen symexec` on CFG bodies -/

/-- A price with two discounts, as a CFG; the bulk discount is too large at exactly 10 items,
    so `p_pos` fails on the two paths through the bulk discount. -/
private def pricePgm : StrataDDM.Program :=
#strata
program Core;
procedure Price(qty : int, member : bool, out p : int)
spec {
  requires [qty_pos]: int.gt(qty, 0);
  ensures [p_pos]: int.gt(p, 0);
}
cfg entry {
  entry: { p := int.mul(qty, 10); branch (member) goto disc else goto bulkCheck; }
  disc: { p := int.sub(p, 5); goto bulkCheck; }
  bulkCheck: { branch (int.ge(qty, 10)) goto bulk else goto done; }
  bulk: { p := int.sub(p, 100); goto done; }
  done: { assert [p_le_list]: int.le(p, int.mul(qty, 10)); return; }
};
#end

/-- info: "p_le_list: ✅ pass\np_pos: ❌ fail (fail on 2 paths, pass on 2 paths)" -/
#guard_msgs in
#eval verifyCFG pricePgm
/-- info: "p_le_list: ✅ pass\np_pos: ❌ fail" -/
#guard_msgs in
#eval verifyCFG pricePgm .always
/-- info: "p_le_list: ✅ pass\np_pos: ❌ fail" -/
#guard_msgs in
#eval verifyCFG pricePgm (.pathsAbove 2)

-- Without `--vcgen symexec`, the legacy symbolic evaluator cannot verify a CFG body, and the
-- verifier refuses it.
/--
info: error: ❌ Expected every procedure body to be structured, but found procedure Price with a CFG body. To verify it, pass --vcgen symexec (for an acyclic one) or --vcgen usp (or uwp).
-/
#guard_msgs (whitespace := lax) in
#eval do
  let (coreProg, _) := Strata.Core.getProgram pricePgm
  try
    let _ ← EIO.toIO (fun e => IO.Error.userError (toString e))
      (Strata.Core.verifyProgram coreProg { Core.VerifyOptions.default with verbose := .quiet })
    IO.println "verified"
  catch e => IO.println s!"error: {withoutRange (toString e)}"

-- A loop in a CFG body is cut at its header (`cfgLoopElim`), using the header's invariant.
/--
info: "cfgLoopElimAssert_entry_loop_0: ✅ pass\ncfgLoopElimAssert_maintain_loop_body_0:
  ✅ pass\neq: ✅ pass"
-/
#guard_msgs (whitespace := lax) in
#eval verifyCFG <|
#strata
program Core;
procedure P(n : int, out y : int)
spec { requires [nneg]: int.ge(n, 0); ensures [eq]: y == n; }
cfg entry {
  entry: { y := 0; goto loop; }
  @[loopInvariant = (int.le(y, n))]
  loop: { branch (int.lt(y, n)) goto body else goto done; }
  body: { y := int.add(y, 1); goto loop; }
  done: { return; }
};
#end

-- A call in a block on a cycle: the loop is cut before call elimination, so the call's `init`s
-- are in an acyclic body, and the invariant gives the callee's precondition.
/--
info: "cfgLoopElimAssert_entry_loop_0: ✅ pass\ncallElimAssert_inc_pre_2:
  ✅ pass\ncfgLoopElimAssert_maintain_loop_body_0: ✅ pass"
-/
#guard_msgs (whitespace := lax) in
#eval verifyCFG <|
#strata
program Core;
procedure Inc(x : int, out y : int)
spec { requires [inc_pre]: int.ge(x, 0); free ensures [inc_post]: y == int.add(x, 1); };
procedure P(n : int, out y : int)
spec { requires [nneg]: int.ge(n, 0); }
cfg entry {
  entry: { y := 0; goto loop; }
  @[loopInvariant = (int.ge(y, 0))]
  loop: { branch (int.lt(y, n)) goto body else goto done; }
  body: { call Inc(y, out y); goto loop; }
  done: { return; }
};
#end

-- Calls in a CFG block to a procedure with a contract and no body are eliminated in place: each
-- call's precondition is checked there and its postcondition assumed.
/--
info: "callElimAssert_q_pre_2: ❌ fail\ncallElimAssert_q_pre_6: ✅ pass\nr_gt_t: ✅ pass\nr_big: ✅
  pass"
-/
#guard_msgs (whitespace := lax) in
#eval verifyCFG <|
#strata
program Core;
procedure Q(x : int, out r : int)
spec { requires [q_pre]: int.gt(x, 0); free ensures [q_post]: int.gt(r, x); };
procedure P(x : int, out t : int, out r : int)
spec { requires [x_nneg]: int.ge(x, 0); ensures [r_big]: int.gt(r, 1); }
cfg entry {
  entry: { call Q(x, out t); call Q(t, out r); goto done; }
  done: { assert [r_gt_t]: int.gt(r, t); return; }
};
#end

-- A partial function in a block command and in a branch condition: the command's call is
-- checked before the command, and the branch condition's at the end of its block.
/-- info: "set_r_calls_Int.SafeDiv_0: ✅ pass\nbranch_cond_calls_Int.SafeDiv_0: ❌ fail" -/
#guard_msgs (whitespace := lax) in
#eval verifyCFG <|
#strata
program Core;
procedure P(x : int, y : int, out r : int)
spec { requires [y_nz]: !(y == 0); }
cfg entry {
  entry: { r := int.safeDiv(x, y);
    branch (int.gt(int.safeDiv(x, int.sub(y, 1)), 0)) goto pos else goto done; }
  pos: { r := int.add(r, 1); goto done; }
  done: { return; }
};
#end

-- A polymorphic procedure with a CFG body: its type parameter becomes an opaque type
-- (`genOpaqueTypeParams`) in the commands, the local declaration and the branch guard.
/-- info: "r_eq: ✅ pass\nr_is_arg: ✅ pass" -/
#guard_msgs (whitespace := lax) in
#eval verifyCFG <|
#strata
program Core;
procedure Pick<T>(c : bool, x : T, y : T, out r : T)
spec { ensures [r_is_arg]: (r == x) || (r == y); }
cfg entry {
  entry: { var z : T := y; branch (c) goto a else goto b; }
  a: { r := x; goto done; }
  b: { r := z; goto done; }
  done: { assert [r_eq]: (r == x) || (r == z); return; }
};
#end

/-! ## Calls between structured and CFG procedures

Call elimination replaces a call by the callee's contract: its precondition is checked at the
call and its postcondition assumed after it. The callee's own body is verified against its
contract. Each program is verified under merge policies `never` and `always`. -/

-- A structured caller and a CFG callee.
private def absCallerPgm : StrataDDM.Program :=
#strata
program Core;
procedure Abs(x : int, out r : int)
spec { ensures [abs_nonneg]: int.ge(r, 0); ensures [abs_ge_x]: int.ge(r, x); }
cfg entry {
  entry: { branch (int.ge(x, 0)) goto pos else goto neg; }
  pos: { r := x; goto done; }
  neg: { r := int.neg(x); goto done; }
  done: { return; }
};
procedure Caller(y : int, out z : int) {
  call Abs(y, out z);
  assert [z_nonneg]: int.ge(z, 0);
  assert [z_ge_y]: int.ge(z, y);
};
#end

/--
info: never:
abs_nonneg: ✅ pass
abs_ge_x: ✅ pass
z_nonneg: ✅ pass
z_ge_y: ✅ pass
always:
abs_nonneg: ✅ pass
abs_ge_x: ✅ pass
z_nonneg: ✅ pass
z_ge_y: ✅ pass
-/
#guard_msgs in
#eval verifyNeverAlways absCallerPgm

-- The caller asserts more than the callee's contract gives: `z` is 0 when `y` is 0. A model
-- found under a call's assumed postcondition is not confirmed, so the check is unknown.
private def absCallerFailPgm : StrataDDM.Program :=
#strata
program Core;
procedure Abs(x : int, out r : int)
spec { ensures [abs_nonneg]: int.ge(r, 0); ensures [abs_ge_x]: int.ge(r, x); }
cfg entry {
  entry: { branch (int.ge(x, 0)) goto pos else goto neg; }
  pos: { r := x; goto done; }
  neg: { r := int.neg(x); goto done; }
  done: { return; }
};
procedure Caller(y : int, out z : int) {
  call Abs(y, out z);
  assert [z_pos]: int.gt(z, 0);
};
#end

/--
info: never:
abs_nonneg: ✅ pass
abs_ge_x: ✅ pass
z_pos: ❓ unknown
always:
abs_nonneg: ✅ pass
abs_ge_x: ✅ pass
z_pos: ❓ unknown
-/
#guard_msgs in
#eval verifyNeverAlways absCallerFailPgm

-- The callee's body breaks `abs_nonneg` through `neg`; the caller, which relies on the
-- contract, still passes.
private def absCalleeFailPgm : StrataDDM.Program :=
#strata
program Core;
procedure Abs(x : int, out r : int)
spec { ensures [abs_nonneg]: int.ge(r, 0); ensures [abs_ge_x]: int.ge(r, x); }
cfg entry {
  entry: { branch (int.ge(x, 0)) goto pos else goto neg; }
  pos: { r := x; goto done; }
  neg: { r := x; goto done; }
  done: { return; }
};
procedure Caller(y : int, out z : int) {
  call Abs(y, out z);
  assert [z_nonneg]: int.ge(z, 0);
  assert [z_ge_y]: int.ge(z, y);
};
#end

/--
info: never:
abs_nonneg: ❌ fail (fail on 1 path, pass on 1 path)
abs_ge_x: ✅ pass
z_nonneg: ✅ pass
z_ge_y: ✅ pass
always:
abs_nonneg: ❌ fail
abs_ge_x: ✅ pass
z_nonneg: ✅ pass
z_ge_y: ✅ pass
-/
#guard_msgs in
#eval verifyNeverAlways absCalleeFailPgm

-- A CFG caller and a structured callee, called once on one branch and twice on the other.
private def incCallerPgm : StrataDDM.Program :=
#strata
program Core;
procedure Inc(x : int, out y : int)
spec { ensures [inc_post]: y == int.add(x, 1); }
{ y := int.add(x, 1); };
procedure Caller(x : int, out r : int)
spec { ensures [caller_post]: int.gt(r, x); }
cfg entry {
  entry: { branch (int.gt(x, 0)) goto pos else goto neg; }
  pos: { call Inc(x, out r); goto done; }
  neg: { call Inc(x, out r); call Inc(r, out r); goto done; }
  done: { assert [r_gt_x]: int.gt(r, x); return; }
};
#end

/--
info: never:
inc_post: ✅ pass
r_gt_x: ✅ pass
caller_post: ✅ pass
always:
inc_post: ✅ pass
r_gt_x: ✅ pass
caller_post: ✅ pass
-/
#guard_msgs in
#eval verifyNeverAlways incCallerPgm

-- The caller asserts `r > x + 1`, which holds only on the branch through `neg`; on the other
-- branch the model, found under a call's assumed postcondition, is not confirmed.
private def incCallerFailPgm : StrataDDM.Program :=
#strata
program Core;
procedure Inc(x : int, out y : int)
spec { ensures [inc_post]: y == int.add(x, 1); }
{ y := int.add(x, 1); };
procedure Caller(x : int, out r : int)
cfg entry {
  entry: { branch (int.gt(x, 0)) goto pos else goto neg; }
  pos: { call Inc(x, out r); goto done; }
  neg: { call Inc(x, out r); call Inc(r, out r); goto done; }
  done: { assert [r_gt_x1]: int.gt(r, int.add(x, 1)); return; }
};
#end

/--
info: never:
inc_post: ✅ pass
r_gt_x1: ❓ unknown (pass on 1 path, unknown on 1 path)
always:
inc_post: ✅ pass
r_gt_x1: ❓ unknown
-/
#guard_msgs in
#eval verifyNeverAlways incCallerFailPgm

-- The callee's body breaks `inc_post`; the caller, which relies on the contract, still passes.
private def incCalleeFailPgm : StrataDDM.Program :=
#strata
program Core;
procedure Inc(x : int, out y : int)
spec { ensures [inc_post]: y == int.add(x, 1); }
{ y := x; };
procedure Caller(x : int, out r : int)
spec { ensures [caller_post]: int.gt(r, x); }
cfg entry {
  entry: { branch (int.gt(x, 0)) goto pos else goto neg; }
  pos: { call Inc(x, out r); goto done; }
  neg: { call Inc(x, out r); call Inc(r, out r); goto done; }
  done: { assert [r_gt_x]: int.gt(r, x); return; }
};
#end

/--
info: never:
inc_post: ❌ fail
r_gt_x: ✅ pass
caller_post: ✅ pass
always:
inc_post: ❌ fail
r_gt_x: ✅ pass
caller_post: ✅ pass
-/
#guard_msgs in
#eval verifyNeverAlways incCalleeFailPgm

/-! ## Where the branches of a fork first meet

In a CFG with no cycle, a fork joins at the block of those both its successors reach that has no
predecessor among them (a path may bypass it), or at the forking block's immediate
post-dominator if there is no single such block; a join never lies outside
the path's innermost open join; a path has left the branches once its block cannot reach the
join's block. In a CFG with a cycle, a fork joins at the immediate post-dominator. On a body
lowered from structured statements (`Core.stmtsToCFG`), the CFG run merges wherever the
structured run does. It also merges an exiting path at the end of the block it exits when the
last `if` before that end joins there (the families below), and it differs in the two cases
pinned at the end of this section. -/

/-- The join a fork at block `b` of `g` opens (`cfgShape`'s `forkSite`) on a path whose
    innermost open join is at block `head` (`none`: no open join): `some j` for block `j`,
    `none` for no join. -/
private def joinOf (g : Core.DetCFG) (b : String) (head : Option String := none) :
    Option String :=
  letI := symLang {}
  let env : IEnv Expression := { store := IStore.ofStore (fun _ => none), factory := Core.Factory }
  match g.blocks.lookup b with
  | some blk =>
    match (cfgShape {} g).forkSite (head.map .block) (.inBlock g b [] blk.transfer env) with
    | some (.block j) => some j
    | _ => none
  | none => none

-- A diamond, and a branch that skips one side: the join is the immediate post-dominator.
#guard joinOf diamondG "E" == some "J"
#guard joinOf sharedG "E" == some "J" && joinOf sharedG "A" == some "J"

-- A branch whose two targets are the same block joins there.
#guard joinOf (graph "E" [("E", ["A", "A"]), ("A", [])]) "E" == some "A"

/-- One successor of `E` can leave by `A → X` without passing `J`: the immediate
    post-dominator of `E` is `X`, but both sides first meet at `J`. -/
private def leaveG := graph "E" [("E", ["A", "J"]), ("A", ["X", "J"]), ("J", ["X"]), ("X", [])]
#guard (ipdomList leaveG).lookup "E" == some (some "X")
#guard joinOf leaveG "E" == some "J"

/-- `P` and `Q` are both first blocks the two sides reach: the fork falls back to the
    immediate post-dominator, `X`. -/
private def twoFirstG := graph "E"
  [("E", ["A", "B"]), ("A", ["P", "Q"]), ("B", ["P", "Q"]), ("P", ["X"]), ("Q", ["X"]),
   ("X", [])]
#guard joinOf twoFirstG "E" == some "X"

/-- A nested fork whose first common block lies past the outer join: `E` joins at `H`; `A`,
    inside `E`'s branches, would join at `X`, which `H` does not reach. -/
private def clampG := graph "E"
  [("E", ["A", "H"]), ("A", ["P", "Q"]), ("P", ["H", "X"]), ("Q", ["X"]), ("H", ["X"]),
   ("X", [])]
#guard joinOf clampG "E" == some "H"
#guard joinOf clampG "A" == some "X"
-- On a path whose innermost open join is at `H`, `A`'s fork joins at `H` instead.
#guard joinOf clampG "A" (head := some "H") == some "H"

/-- Whether a path at block `l` of `g` has left the branches of a fork that joins at block `j`
    (`cfgShape`'s `passedJoin`). -/
private def passedAt (g : Core.DetCFG) (j l : String) : Bool :=
  letI := symLang {}
  let env : IEnv Expression := { store := IStore.ofStore (fun _ => none), factory := Core.Factory }
  (cfgShape {} g).passedJoin (.block j) (.atBlock g l env)

-- `X` cannot reach `H`, so a path there has left; `P` can, so a path there has not.
#guard passedAt clampG "H" "X" && !passedAt clampG "H" "P"

-- With a cycle the join is the immediate post-dominator: `H` joins at `X`.
#guard joinOf loopG "H" == some "X"

/-- `p` with its structured body lowered to a CFG (`Core.stmtsToCFG`). -/
private def lowered (p : Option Procedure) : Option Procedure :=
  p.bind fun p => match p.body with
    | .structured ss _ => (Core.stmtsToCFG ss).map fun g => { p with body := .cfg g false }
    | .cfg _ _ | .abstract => none

/-- Paths finished and merges of `run p` under `MergePolicy.always`. -/
private def counts (p : Option Procedure) : Option (Nat × Nat) :=
  (run p .always).map fun r => (r.finished, r.merges)

/-- One `if` in block `B`, each with an `exit B` nested in its then-branch. -/
private def exitFamily1 := procOf <|
#strata
program Core;
procedure P(x : int, y : int, out r : int) {
  r := 0;
  B: {
    if (int.gt(x, 0)) {
      if (int.gt(y, 0)) { exit B; } else { }
      r := int.add(r, 1);
    } else { r := int.mul(r, 2); }
  }
  assert [nonneg]: int.ge(r, 0);
};
#end

-- Structured: 2 paths and 1 merge. Lowered: 1 path and 2 merges; the last `if` joins at
-- the block after `B`, where the exits land, so one exiting path merges there too.
/-- info: (some (2, 1), some (1, 2)) -/
#guard_msgs in
#eval (counts exitFamily1, counts (lowered exitFamily1))

/-- Two `if`s in block `B`, each with an `exit B` nested in its then-branch. -/
private def exitFamily2 := procOf <|
#strata
program Core;
procedure P(x : int, y : int, out r : int) {
  r := 0;
  B: {
    if (int.gt(x, 0)) {
      if (int.gt(y, 0)) { exit B; } else { }
      r := int.add(r, 1);
    } else { r := int.mul(r, 2); }
    if (int.gt(x, 1)) {
      if (int.gt(y, 1)) { exit B; } else { }
      r := int.add(r, 1);
    } else { r := int.mul(r, 2); }
  }
  assert [nonneg]: int.ge(r, 0);
};
#end

-- Structured: 3 paths and 2 merges. Lowered: 2 paths and 3 merges.
/-- info: (some (3, 2), some (2, 3)) -/
#guard_msgs in
#eval (counts exitFamily2, counts (lowered exitFamily2))

/-- Fourteen `if`s in block `B`, each with an `exit B` nested in its then-branch. -/
private def exitFamily14 := procOf <|
#strata
program Core;
procedure P(x : int, y : int, out r : int) {
  r := 0;
  B: {
    if (int.gt(x, 0)) {
      if (int.gt(y, 0)) { exit B; } else { }
      r := int.add(r, 1);
    } else { r := int.mul(r, 2); }
    if (int.gt(x, 1)) {
      if (int.gt(y, 1)) { exit B; } else { }
      r := int.add(r, 1);
    } else { r := int.mul(r, 2); }
    if (int.gt(x, 2)) {
      if (int.gt(y, 2)) { exit B; } else { }
      r := int.add(r, 1);
    } else { r := int.mul(r, 2); }
    if (int.gt(x, 3)) {
      if (int.gt(y, 3)) { exit B; } else { }
      r := int.add(r, 1);
    } else { r := int.mul(r, 2); }
    if (int.gt(x, 4)) {
      if (int.gt(y, 4)) { exit B; } else { }
      r := int.add(r, 1);
    } else { r := int.mul(r, 2); }
    if (int.gt(x, 5)) {
      if (int.gt(y, 5)) { exit B; } else { }
      r := int.add(r, 1);
    } else { r := int.mul(r, 2); }
    if (int.gt(x, 6)) {
      if (int.gt(y, 6)) { exit B; } else { }
      r := int.add(r, 1);
    } else { r := int.mul(r, 2); }
    if (int.gt(x, 7)) {
      if (int.gt(y, 7)) { exit B; } else { }
      r := int.add(r, 1);
    } else { r := int.mul(r, 2); }
    if (int.gt(x, 8)) {
      if (int.gt(y, 8)) { exit B; } else { }
      r := int.add(r, 1);
    } else { r := int.mul(r, 2); }
    if (int.gt(x, 9)) {
      if (int.gt(y, 9)) { exit B; } else { }
      r := int.add(r, 1);
    } else { r := int.mul(r, 2); }
    if (int.gt(x, 10)) {
      if (int.gt(y, 10)) { exit B; } else { }
      r := int.add(r, 1);
    } else { r := int.mul(r, 2); }
    if (int.gt(x, 11)) {
      if (int.gt(y, 11)) { exit B; } else { }
      r := int.add(r, 1);
    } else { r := int.mul(r, 2); }
    if (int.gt(x, 12)) {
      if (int.gt(y, 12)) { exit B; } else { }
      r := int.add(r, 1);
    } else { r := int.mul(r, 2); }
    if (int.gt(x, 13)) {
      if (int.gt(y, 13)) { exit B; } else { }
      r := int.add(r, 1);
    } else { r := int.mul(r, 2); }
  }
  assert [nonneg]: int.ge(r, 0);
};
#end

-- Structured: 15 paths and 14 merges. Lowered: 14 paths and 15 merges.
/-- info: (some (15, 14), some (14, 15)) -/
#guard_msgs in
#eval (counts exitFamily14, counts (lowered exitFamily14))

/-- Two `if`s in block `B`, each side of which may `exit B`. -/
private def bothLeave2 := procOf <|
#strata
program Core;
procedure P(x : int, y : int, z : int, out r : int) {
  r := 0;
  B: {
    if (int.gt(x, 0)) { if (int.gt(y, 0)) { exit B; } else { } }
    else { if (int.gt(z, 0)) { exit B; } else { } }
    if (int.gt(x, 1)) { if (int.gt(y, 1)) { exit B; } else { } }
    else { if (int.gt(z, 1)) { exit B; } else { } }
  }
  assert [nonneg]: int.ge(r, 0);
};
#end

-- Both sides first meet at the next `if`: structured 5 paths, 2 merges; lowered
-- 3 paths, 4 merges, the two exits of the last `if` merging after `B`.
/-- info: (some (5, 2), some (3, 4)) -/
#guard_msgs in
#eval (counts bothLeave2, counts (lowered bothLeave2))

/-- Fourteen `if`s in block `B`, each side of which may `exit B`. -/
private def bothLeave14 := procOf <|
#strata
program Core;
procedure P(x : int, y : int, z : int, out r : int) {
  r := 0;
  B: {
    if (int.gt(x, 0)) { if (int.gt(y, 0)) { exit B; } else { } }
    else { if (int.gt(z, 0)) { exit B; } else { } }
    if (int.gt(x, 1)) { if (int.gt(y, 1)) { exit B; } else { } }
    else { if (int.gt(z, 1)) { exit B; } else { } }
    if (int.gt(x, 2)) { if (int.gt(y, 2)) { exit B; } else { } }
    else { if (int.gt(z, 2)) { exit B; } else { } }
    if (int.gt(x, 3)) { if (int.gt(y, 3)) { exit B; } else { } }
    else { if (int.gt(z, 3)) { exit B; } else { } }
    if (int.gt(x, 4)) { if (int.gt(y, 4)) { exit B; } else { } }
    else { if (int.gt(z, 4)) { exit B; } else { } }
    if (int.gt(x, 5)) { if (int.gt(y, 5)) { exit B; } else { } }
    else { if (int.gt(z, 5)) { exit B; } else { } }
    if (int.gt(x, 6)) { if (int.gt(y, 6)) { exit B; } else { } }
    else { if (int.gt(z, 6)) { exit B; } else { } }
    if (int.gt(x, 7)) { if (int.gt(y, 7)) { exit B; } else { } }
    else { if (int.gt(z, 7)) { exit B; } else { } }
    if (int.gt(x, 8)) { if (int.gt(y, 8)) { exit B; } else { } }
    else { if (int.gt(z, 8)) { exit B; } else { } }
    if (int.gt(x, 9)) { if (int.gt(y, 9)) { exit B; } else { } }
    else { if (int.gt(z, 9)) { exit B; } else { } }
    if (int.gt(x, 10)) { if (int.gt(y, 10)) { exit B; } else { } }
    else { if (int.gt(z, 10)) { exit B; } else { } }
    if (int.gt(x, 11)) { if (int.gt(y, 11)) { exit B; } else { } }
    else { if (int.gt(z, 11)) { exit B; } else { } }
    if (int.gt(x, 12)) { if (int.gt(y, 12)) { exit B; } else { } }
    else { if (int.gt(z, 12)) { exit B; } else { } }
    if (int.gt(x, 13)) { if (int.gt(y, 13)) { exit B; } else { } }
    else { if (int.gt(z, 13)) { exit B; } else { } }
  }
  assert [nonneg]: int.ge(r, 0);
};
#end

-- Structured: 29 paths and 14 merges. Lowered: 27 paths and 16 merges.
/-- info: (some (29, 14), some (27, 16)) -/
#guard_msgs in
#eval (counts bothLeave14, counts (lowered bothLeave14))

/-- 2 `if`s whose then-branch holds an inner `if`, then a possible `exit B`. -/
private def innerJoin2 := procOf <|
#strata
program Core;
procedure P(x : int, y : int, z : int, out r : int) {
  r := 0;
  B: {
    if (int.gt(x, 0)) {
      if (int.gt(y, 0)) { r := int.add(r, 1); } else { r := int.add(r, 2); }
      r := int.mul(r, 2);
      if (int.gt(z, 0)) { exit B; } else { }
    } else { r := int.add(r, 3); }
    if (int.gt(x, 1)) {
      if (int.gt(y, 1)) { r := int.add(r, 1); } else { r := int.add(r, 2); }
      r := int.mul(r, 2);
      if (int.gt(z, 1)) { exit B; } else { }
    } else { r := int.add(r, 3); }
  }
  assert [nonneg]: int.ge(r, 0);
};
#end

-- The inner `if`s join at their own end, inside the outer join: structured 3 paths, 4 merges;
-- lowered 2 paths, 5 merges, the last exit merging after `B`.
/-- info: (some (3, 4), some (2, 5)) -/
#guard_msgs in
#eval (counts innerJoin2, counts (lowered innerJoin2))

/-- A path that leaves: from `a` a path can return without passing `j`, where the other paths
    meet. -/
private def leaves := procOf <|
#strata
program Core;
procedure P(x : int, out r : int)
cfg entry {
  entry: { branch (int.gt(x, 0)) goto a else goto b; }
  a: { branch (int.gt(x, 5)) goto ret else goto j; }
  ret: { r := 1; return; }
  b: { goto j; }
  j: { r := 2; assert [at_j]: int.ge(r, 0); return; }
};
#end

-- Per path, three paths and two obligations for `at_j`; merged, the two paths through `j` meet
-- there: two paths, one obligation for `at_j`, one merge.
/-- info: some { finished := 3, stopped := 0, obligations := 2, merges := 0, unreached := 0 } -/
#guard_msgs in
#eval summary leaves
/-- info: some { finished := 2, stopped := 0, obligations := 1, merges := 1, unreached := 0 } -/
#guard_msgs in
#eval summary leaves .always

/-- `leaves` with a local declared on each side before `j`, under the same name: each is dropped
    at the merge, so the merge happens. -/
private def leavesLocals := procOf <|
#strata
program Core;
procedure P(x : int, out r : int)
cfg entry {
  entry: { branch (int.gt(x, 0)) goto a else goto b; }
  a: { branch (int.gt(x, 5)) goto ret else goto a2; }
  ret: { r := 1; return; }
  a2: { var t : int := 1; r := t; goto j; }
  b: { var t : int := 2; r := t; goto j; }
  j: { assert [at_j]: int.ge(r, 0); return; }
};
#end

/-- info: some { finished := 2, stopped := 0, obligations := 1, merges := 1, unreached := 0 } -/
#guard_msgs in
#eval summary leavesLocals .always

/-- `leaves` with a local declared on one side only. -/
private def leavesLocal := procOf <|
#strata
program Core;
procedure P(x : int, out r : int)
cfg entry {
  entry: { branch (int.gt(x, 0)) goto a else goto b; }
  a: { branch (int.gt(x, 5)) goto ret else goto a2; }
  ret: { r := 1; return; }
  a2: { var t : int := 1; r := t; goto j; }
  b: { r := 2; goto j; }
  j: { assert [at_j]: int.ge(r, 0); return; }
};
#end

/-- info: some { finished := 2, stopped := 0, obligations := 1, merges := 1, unreached := 0 } -/
#guard_msgs in
#eval summary leavesLocal .always

/-- Both sides of the inner `if`s may leave `L2`, and both continue to `r := 0` or to the block
    after `L2`: two first common blocks, so the lowered run falls back to the immediate
    post-dominator, while the structured run joins at the end of the `if`. -/
private def twoFirst := procOf <|
#strata
program Core;
procedure P(x : int, y : int, z : int, out r : int) {
  r := 1;
  L3: {
    L2: {
      if (int.gt(x, 0)) { if (int.gt(y, 0)) { exit L2; } else { } }
      else { if (int.gt(z, 0)) { exit L2; } else { } }
      r := 0;
      exit L3;
    }
    r := 5;
  }
  assert [nonneg]: int.ge(r, 0);
};
#end

-- Structured first, lowered second.
/-- info: (some (3, 1), some (1, 3)) -/
#guard_msgs in
#eval (counts twoFirst, counts (lowered twoFirst))

/-- A then-branch that always exits, to `L1` or to `L2`: the lowered run joins at the block
    after `L1`, the first both sides reach; the structured run joins at the end of `L2`, the
    block that catches every exit. -/
private def twoTargets := procOf <|
#strata
program Core;
procedure P(x : int, y : int, out r : int) {
  r := 1;
  L2: {
    L1: {
      if (int.gt(x, 0)) { if (int.gt(y, 0)) { exit L1; } else { exit L2; } } else { }
      r := 2;
    }
    r := int.add(r, 3);
  }
  assert [nonneg]: int.ge(r, 0);
};
#end

-- Structured first, lowered second.
/-- info: (some (1, 2), some (2, 1)) -/
#guard_msgs in
#eval (counts twoTargets, counts (lowered twoTargets))

end SymExecCFGTest

end -- meta section
