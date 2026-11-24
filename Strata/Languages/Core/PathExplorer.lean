/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.SymExec
public import Strata.Languages.Core.StatementEval
public import Strata.Languages.Core.Options
public import Strata.DL.Imperative.InterpreterCFG
public import Strata.DL.Imperative.CFGDominators
public import Strata.Languages.Core.WF
public import Std.Data.HashSet

/-! # The path explorer

`explore` runs a monad-generic engine one step at a time, in `ForkM`, from outside the monad:
`stepInterp` for a structured body, `stepInterpCFG` for a CFG body. What the explorer needs to
know about either kind of configuration (how to step it, where the branches of a fork meet
again, how to merge two paths there) is a `ProcBodyShape`: `structuredShape` and `cfgShape`.
That lets the explorer

* keep the paths as an explicit worklist and record them as a tree (`Node`, `Result`);
* stop paths where the branches of a fork first meet again, wait for both branches, and let a
  `MergePolicy` (any Lean function of a `JoinView`) decide whether to merge them (`placeF`,
  `joinBranchesF`, `mergeBranches`, `mergeEnvs`), naming each merged value by a fresh symbol
  defined in the path condition (`nameJoinValues`). The branches meet at the end of an `if`, or,
  when one branch always exits, at the end of the labelled block that catches its `exit`s; in a
  CFG with no cycle, at the block of those both successors of the forking block reach that has
  no predecessor among them (a path may bypass it); in a CFG with a cycle, at the forking block's
  immediate post-dominator (`cfgShape` has the details);
* record the `assert`s and `cover`s that no path reaches in `Result.unreached`. A check is told
  apart by its label and metadata (`Imperative.AssertId`), and the run records the checks some
  path reaches (`Result.reached`). A check in an `if` branch that no path entered at a decided
  guard is reported at the `if` (`deadBranchObls`, under the path condition there); when the run
  is complete, `Result.addUnreached` adds every other check of the body no path reached. What an
  unreached check means is up to the client: the verifier reports it as unreachable;
* bound the work per path (`runFuel`) and in total (`maxSteps`), and the number of paths
  (`ExploreCfg.maxPaths`); a run that stops early says so (`Result.completeness`);
* end a path at a step that adds a path-condition entry that is literal `false`
  (`infeasibleStatus`): no run follows it, so the explorer neither explores nor merges it, and
  the checks only it would reach are reported unreached.

`exploreProc` sets up one procedure and calls `explore`; `symExecProgram`, the entry point of
symbolic execution for verification, checks `symExecRequires` and runs every procedure.
-/

namespace Core.SymExec

open Imperative Lambda

public section

/-! ## Exploring paths -/

/-- How a path ended (or `running` while it has not). -/
inductive NodeStatus where
  | running
  /-- Forked into children. -/
  | forked
  | finished
  /-- The path stopped: run budget exhausted (`replayFuelExhausted`), a condition that did not
      evaluate (`interrupted` with the reason), or a program error. -/
  | stopped (r : StopReason)
  /-- The total work bound `maxSteps` ran out before this path ended. -/
  | outOfWork
  /-- An `exit` that no enclosing block matched. -/
  | unmatchedExit (label : String)
  /-- Merged with its sibling at the join of the `if` that forked them; the merged path
      continues in the fork node's `cont`. -/
  | joined
  /-- Not explored further: the run reached its path limit (`ExploreCfg.maxPaths`). -/
  | overPathLimit
  /-- Ended at the step that added the path-condition entry labelled `label`, which is literal
      `false`, so no run follows the path past it (`infeasibleStatus`). -/
  | infeasible (label : String)

/-- A node of the path tree: the condition added when it was created by a fork, and the
    obligations recorded on it, in emission order. -/
structure Node where
  parent : Option Nat
  cond : Option Expression.Expr
  /-- The path condition when the node was created (for a fork child: including the fork's
      condition), newest first. -/
  startPc : List (String × Expression.Expr) := []
  obls : Array Obl := #[]
  status : NodeStatus := .running
  /-- For a node that forked: the node where its branches' merged path continues, if they
      merged. -/
  cont : Option Nat := none

/-- The result of a run: the path tree as an array (root at index 0). Whether it covers the
    whole procedure is read from the node statuses (`Result.completeness`). -/
structure Result where
  nodes : Array Node
  /-- Steps taken. -/
  steps : Nat
  /-- The checks no path reached. Each is stated as a dead-branch obligation: a path condition
      ending in a `false` entry, with a literal goal (`true` for an assert, `false` for a
      cover). A check in an `if` branch that some path skipped at a
      decided guard `g` and no path entered is reported under that path's condition at the `if`
      plus `<dead_branch: g>` (`deadBranchObls`), once per such path. When the run is complete,
      every other check of the body no path reached is reported once, under only
      `<unreachable_block: l>` in a CFG body (`l` the check's block, in block and command order)
      and `<unreachable_check: a>` in a structured body (`a` the check's label, in statement
      order). What they mean is up to the client; the verifier reports each as unreachable.
      Filled in by `explore` and `Result.addUnreached`. -/
  unreached : List Obl := []
  /-- The checks some path reached, told apart by label and metadata as `Imperative.AssertId`
      does: for each label, the metadata of the reached checks with that label. Two checks with
      the same label and the same metadata are one check here, so reaching either accounts for
      both. -/
  reached : Std.HashMap String (Array (MetaData Expression)) := {}
  /-- Joins at which two paths were merged. -/
  merges : Nat := 0
  /-- Merged values left unnamed at joins because their variable's declared type was not
      recorded on the then-branch or differs on the else-branch (`nameJoinStep`); expected to be
      0. Function-typed values, never named, are not counted. -/
  joinValuesUnnamed : Nat := 0
  /-- The run's start: each formal (and `old` name) with the symbol it was bound to. -/
  entry : List (CoreIdent × Expression.Expr) := []
  /-- For a structured body, the statements the run executed (precondition assumes, body,
      checked postconditions). -/
  stmts : List Statement := []
  /-- For a CFG body, the CFG the run executed (`wrapCFG`: the body's blocks, with an entry
      block assuming the preconditions and an exit block checking the postconditions). -/
  graph : Option Core.DetCFG := none

/-! ## Reading results -/

/-- All obligations, in node order. -/
def Result.obligations (r : Result) : List Obl :=
  r.nodes.toList.flatMap (·.obls.toList)

/-- How many nodes have a status satisfying `f`. -/
def Result.countStatus (r : Result) (f : NodeStatus → Bool) : Nat :=
  r.nodes.foldl (fun n nd => if f nd.status then n + 1 else n) 0

/-- Paths that finished. -/
def Result.finished (r : Result) : Nat :=
  r.countStatus fun | .finished => true | _ => false
/-- Paths that stopped. -/
def Result.stopped (r : Result) : Nat :=
  r.countStatus fun | .stopped _ => true | _ => false
/-- Paths pending when the work bound ran out. -/
def Result.outOfWork (r : Result) : Nat :=
  r.countStatus fun | .outOfWork => true | _ => false
/-- Paths that exited to an unmatched label. -/
def Result.unmatchedExits (r : Result) : Nat :=
  r.countStatus fun | .unmatchedExit _ => true | _ => false

/-- Whether a run analyzed every way through the procedure. -/
inductive Completeness where
  /-- Every path finished, merged, or ended at a step that added a path-condition entry
      contradicting the rest of its path condition: the obligations cover the procedure. -/
  | complete
  /-- Some path ended before the end of the procedure for the listed reasons (no duplicates,
      in node order): checks past those points have no obligation, so the run says nothing
      about them. -/
  | notAnalyzed (reasons : List String)
  deriving Repr, BEq, DecidableEq

/-- Why a path with this status left part of the procedure unanalyzed, if it did. -/
def NodeStatus.incompleteReason? : NodeStatus → Option String
  | .stopped reason => some s!"a path stopped: {reason}"
  | .outOfWork => some "the work bound ran out"
  | .overPathLimit => some "the path limit was reached"
  | .unmatchedExit l => some s!"a path exited to unmatched label '{l}'"
  | .running => some "a path was left running"
  | _ => none

/-- The run's completeness, from its node statuses (`NodeStatus.incompleteReason?`). -/
def Result.completeness (r : Result) : Completeness :=
  match (r.nodes.toList.filterMap (·.status.incompleteReason?)).eraseDups with
  | [] => .complete
  | reasons => .notAnalyzed reasons

/-! ## Merge policies -/

/-- What a merge policy sees at a join where both branches arrived. -/
structure JoinView where
  /-- The procedure being executed. -/
  proc : String
  /-- How many enclosing forks are still open (0 for an outermost fork). -/
  depth : Nat
  /-- Paths not yet finished, not counting the two branches: those on the worklist and those
      waiting at other joins. -/
  pending : Nat
  /-- Paths that have finished so far. -/
  finished : Nat
  /-- Variables whose values differ between the two branches, computed only if the policy reads
      it; 0 if the branches cannot be merged. -/
  differing : Thunk Nat

/-- Decides, at a join, whether to merge the two branches. It is consulted where each branch
    reached the join as a single path (none left the branches, stopped, or forked without
    merging), before the merge is computed; the branches are merged only if it agrees and they
    can be merged (`mergeBranches`). -/
abbrev MergePolicy := JoinView → Bool

/-- Never merge: one path per way through the procedure (per-path obligations). -/
def MergePolicy.never : MergePolicy := fun _ => false
/-- Merge at every join. -/
def MergePolicy.always : MergePolicy := fun _ => true
/-- Merge whenever more than `n` paths would exist without merging: the two branches plus the
    pending and finished paths. It merges only where the branches can be merged
    (`MergePolicy`), so it does not bound the number of paths; the path limit
    (`ExploreCfg.maxPaths`) does. -/
def MergePolicy.pathsAbove (n : Nat) : MergePolicy := fun v => v.pending + v.finished + 2 > n

/-- The preset a `MergeMode` (`VerifyOptions.symExec`) names. -/
def MergePolicy.ofMode : MergeMode → MergePolicy
  | .never => MergePolicy.never
  | .always => MergePolicy.always
  | .pathsAbove n => MergePolicy.pathsAbove n

/-- Where the branches of a fork meet again. -/
inductive JoinSite where
  /-- The end of the statement whose configuration has `n` sequence and block contexts above it:
      an `if`, or the labelled block around it that catches the `exit`s of a branch that
      always exits (`ifJoinDepth`). -/
  | depth (n : Nat)
  /-- The CFG block `label` where the fork's branches meet (`cfgShape` says which block). -/
  | block (label : String)
  deriving BEq, Repr

/-- A fork whose join is still open, as seen by a path inside one of its branches. -/
structure Join where
  /-- The fork's id (index into the explorer's per-fork tables). -/
  fork : Nat
  /-- Where the branches meet. -/
  site : JoinSite
  /-- The branch: `true` for the then-branch. -/
  side : Bool
  /-- The node that forked. -/
  node : Nat
  /-- The fork's guard (the then-branch assumed it, the else-branch its negation). -/
  guard : Expression.Expr
  /-- The path condition's length at the fork, before the guard. -/
  basePcLen : Nat
  /-- How many entries the path's record of choices (`PathState.choices`) had at the fork. -/
  baseChoices : Nat

/-- Worklist entry: configuration, path state, node, remaining step budget, and the open joins
    of the forks it descends from (innermost first). -/
structure Entry (C : Type) where
  cfg : C
  st : PathState
  node : Nat
  budget : Nat
  joins : List Join := []

/-- The outcomes of one engine step, each with its path state. -/
abbrev Outcomes (C : Type) : Type := List (Out C × PathState)

/-- What the explorer needs to know about a kind of configuration `C` run under `symLang scfg`:
    a structured body's (`structuredShape`) or a CFG body's (`cfgShape`). -/
structure ProcBodyShape (scfg : ExploreCfg) (C : Type) where
  /-- One engine step in `ForkM`, at step budget `fuel`. -/
  step : Nat → C → ForkM C
  /-- How a path at this configuration has ended (`finished`, `unmatchedExit`), if it has. -/
  ended : C → Option NodeStatus
  /-- Where the branches meet if the step at this configuration forks into two continuing
      paths, given the path's innermost open join (`none` if it has none); `none` if such a
      fork opens no join. A path's open joins are innermost first. `placeF` tests only the
      innermost, which suffices when each lies at or inside the next one, as in structured
      bodies and acyclic CFGs (`cfgShape` clamps a join to the innermost open one). In a CFG
      with a cycle a path can reach an outer join while an inner one is open; it is not stopped
      there, so the outer fork's branches are not merged. -/
  forkSite : Option JoinSite → C → Option JoinSite
  /-- Whether a path at this configuration has reached the join at the site. -/
  atJoin : JoinSite → C → Bool
  /-- Whether a path at this configuration has left the fork's branches without reaching the
      join at the site. -/
  passedJoin : JoinSite → C → Bool
  /-- The environment of a path that reached a join. -/
  joinEnv : C → Option (@IEnv Expression (symLang scfg))
  /-- The configuration with the environment at its join replaced. -/
  setJoinEnv : C → @IEnv Expression (symLang scfg) → C
  /-- The environment a branch brings to a merge at the site; it may leave out variables no
      later step can read. -/
  forMerge : JoinSite → @IEnv Expression (symLang scfg) → @IEnv Expression (symLang scfg)
  /-- The obligations for checks a step at this configuration, with these outcomes and this
      path condition, skips: a structured body's `if` at a decided guard (`deadBranchObls`). A
      CFG body has none. The other checks no path reached, in either kind of body, are added
      after the run (`Result.addUnreached`). -/
  deadObls : C → Outcomes C → List (String × Expression.Expr) → List Obl
  /-- The variable the next step at this configuration declares, with its declared type, if
      that step runs an `init` with a monotype (`initDecl?`): the explorer records it in the
      path's `PathState.types` before the step (`stepPath`). -/
  declares : C → Option (CoreIdent × LMonoTy)

/-- The variable a command declares and its declared type, if the command is an `init` whose
    type is a monotype. -/
private def initDecl? : Command → Option (CoreIdent × LMonoTy)
  | .cmd (.init x ty _ _) => ty.toMonoType?.map (x, ·)
  | _ => none

/-- Append obligations (given newest first) to node `i`. -/
private def addObls (nodes : Array Node) (i : Nat) (os : List Obl) : Array Node :=
  nodes.modify i fun n => { n with obls := n.obls ++ os.reverse.toArray }

/-- Set node `i`'s status. -/
private def setStatus (nodes : Array Node) (i : Nat) (s : NodeStatus) : Array Node :=
  nodes.modify i fun n => { n with status := s }

/-! ## Telling checks apart

A check is the label and the metadata of an `assert` or a `cover` (`Imperative.AssertId`), the
identity Strata uses elsewhere: the metadata carries the source location, so two checks written
at different places are different checks. Where the metadata carries no location, two checks
with the same label and the same metadata are one check. -/

/-- The check obligation `o` is about: its label and metadata. -/
private def checkOf (o : Obl) : AssertId Expression := { label := o.label, md := o.md }

/-- Whether the checks `cs` (for each label, their metadata) include `c`: some metadata listed
    under `c`'s label equals `c`'s. -/
private def checkReached (cs : Std.HashMap String (Array (MetaData Expression)))
    (c : AssertId Expression) : Bool :=
  (cs.getD c.label #[]).any (· == c.md)

/-- `cs` with the check `c` added unless `cs` already includes it (`checkReached`). -/
private def addCheck (cs : Std.HashMap String (Array (MetaData Expression)))
    (c : AssertId Expression) : Std.HashMap String (Array (MetaData Expression)) :=
  if checkReached cs c then cs else cs.alter c.label fun mds => some ((mds.getD #[]).push c.md)

/-- The obligation for a check no path reached: the path condition `pcLabel: false` alone, and
    the goal a literal (`true` for an assert, `false` for a cover), stated like the symbolic
    evaluator's dead-branch obligations. -/
private def unreachedObl (kind : OblKind) (pcLabel label : String)
    (md : MetaData Expression) : Obl :=
  { kind, label, md, pc := [(pcLabel, Core.false)],
    cond := if kind == .cover then Core.false else Core.true }

/-- The obligations for the checks of the structured body `ss` when no path reaches them, in
    statement order, under `<unreachable_check: a>: false` (`a` the check's label). -/
private def stmtCheckObls (ss : List Statement) : List Obl :=
  let collect (c : Command) : StateM (Array Obl) Command := do
    match c with
    | .cmd (.assert label _ md) =>
      modify (·.push (unreachedObl .assert s!"<unreachable_check: {label}>" label md))
    | .cmd (.cover label _ md) =>
      modify (·.push (unreachedObl .cover s!"<unreachable_check: {label}>" label md))
    | _ => pure ()
    pure c
  ((Block.mapExprM pure collect ss).run #[]).2.toList

/-- The obligations for the checks of the CFG `g` when no path reaches them, in block and
    command order, under `<unreachable_block: l>: false` (`l` the check's block). -/
private def blockCheckObls (g : Core.DetCFG) : List Obl :=
  g.blocks.flatMap fun (l, b) =>
    let pc := s!"<unreachable_block: {l}>"
    b.cmds.filterMap fun
      | .cmd (.assert label _ md) => some (unreachedObl .assert pc label md)
      | .cmd (.cover label _ md) => some (unreachedObl .cover pc label md)
      | _ => none

/-! ## Structured configurations -/

/-- The engine's configurations for structured statements under `symLang scfg`. -/
abbrev StmtConfig (scfg : ExploreCfg) : Type := @IConfig Expression (symLang scfg) Command

/-- The innermost configuration under the sequence and block contexts: where the next step
    happens. -/
def deepest {scfg : ExploreCfg} (c : StmtConfig scfg) : StmtConfig scfg :=
  letI := symLang scfg
  match c with
  | .seq i _ | .seqs i _ | .block _ _ i => deepest i
  | c => c

/-- The dead-branch obligations of an `if` step: when the step's focus is `if g t e` and some
    outcome continues, every check of a branch no outcome entered (a literal guard, or one the
    path condition decides) gets a dead-branch obligation: the path condition plus
    `<dead_branch: g>: false`, a literal goal, the branch's covers before its asserts. A check
    that an `exit` inside an entered branch skips is not reported here (`Result.addUnreached`
    adds it). -/
private def deadBranchObls {scfg : ExploreCfg} (c : StmtConfig scfg)
    (outs : Outcomes (StmtConfig scfg)) (pc : List (String × Expression.Expr)) : List Obl :=
  letI := symLang scfg
  match deepest c with
  | .stmt (.ite (.det g) t e _) _ =>
    let taken := outs.filterMap fun (o, _) => match o with
      | .ok c' => match deepest c' with | .stmts l _ => some l | _ => none
      | _ => none
    if taken.isEmpty then [] else
    -- A taken branch's statements are normally the `if`'s own list, so `ptrFastEq` usually
    -- decides by pointer identity.
    let dead := [t, e].filter (fun branch => !taken.any (ptrFastEq · branch))
    let pc := (toString f!"<dead_branch: {g.eraseTypes}>", Core.false) :: pc
    dead.flatMap fun branch =>
      (Statement.Statements.collectCovers branch).map (fun (label, md) =>
          { kind := .cover, label, md, pc, cond := Core.false : Obl }) ++
        (Statement.Statements.collectAsserts branch).map fun (label, md) =>
          { kind := .assert, label, md, pc, cond := Core.true : Obl }
  | _ => []

/-- How many sequence and block contexts lie above the innermost configuration. -/
private def wrapperDepth {scfg : ExploreCfg} (c : StmtConfig scfg) : Nat :=
  letI := symLang scfg
  match c with
  | .seq i _ | .seqs i _ | .block _ _ i => wrapperDepth i + 1
  | _ => 0

/-- Replace the innermost configuration. -/
def replaceDeepest {scfg : ExploreCfg} (c new : StmtConfig scfg) : StmtConfig scfg :=
  letI := symLang scfg
  match c with
  | .seq i r => .seq (replaceDeepest i new) r
  | .seqs i k => .seqs (replaceDeepest i new) k
  | .block l f i => .block l f (replaceDeepest i new)
  | _ => new

/-- Whether a path has reached the join at depth `d`: the statement there (the `if`, or the
    labelled block around it) has finished, leaving a terminal configuration at its position. -/
private def stmtAtJoin {scfg : ExploreCfg} (d : Nat) (c : StmtConfig scfg) : Bool :=
  letI := symLang scfg
  wrapperDepth c == d && (match deepest c with | .terminal _ => true | _ => false)

/-- The labelled blocks around the innermost configuration, innermost first, each with the number
    of sequence and block contexts above it. -/
private def enclosingBlocks {scfg : ExploreCfg} (c : StmtConfig scfg) (n : Nat := 0)
    (acc : List (String × Nat) := []) : List (String × Nat) :=
  letI := symLang scfg
  match c with
  | .seq i _ | .seqs i _ | .block none _ i => enclosingBlocks i (n + 1) acc
  | .block (some l) _ i => enclosingBlocks i (n + 1) ((l, n) :: acc)
  | _ => acc

mutual
/-- Whether every way through `s` ends in an `exit` to a block that `s` is not inside of, given
    the labels `inner` of the blocks around `s` that are themselves inside the branch being
    checked: an `exit` to a label not in `inner`; a block whose body always exits (with its own
    label added to `inner`); an `if` both of whose branches always exit. A loop, a command or a
    type declaration does not. -/
private def stmtAlwaysExits (inner : List String) : Statement → Bool
  | .exit l _ => !inner.contains l
  | .block l ss _ => blockAlwaysExits (l :: inner) ss
  | .ite _ t e _ => blockAlwaysExits inner t && blockAlwaysExits inner e
  | _ => false

/-- Whether every way through the statement list `ss` ends in an `exit` past it: one of its
    statements always exits (`stmtAlwaysExits`), so the ones after it are not reached. -/
private def blockAlwaysExits (inner : List String) : List Statement → Bool
  | [] => false
  | s :: ss => stmtAlwaysExits inner s || blockAlwaysExits inner ss
end

/-- The depth of the join of a fork at the `if` with branches `t` and `e`, whose configuration
    `c` has `d` sequence and block contexts above it: where the two branches first meet. If
    neither branch always exits (`blockAlwaysExits`), the end of the `if`: `d`. Otherwise the
    end of the innermost labelled block around the `if` that catches every `exit` of the
    branches that always exit (`Block.checkExitsCoveredByBlocks`); paths that `exit` further
    out pass the join. The join is never outside the path's innermost open join `head` (open
    joins nest), and is `d` if no block around the `if` catches those exits. -/
private def ifJoinDepth {scfg : ExploreCfg} (head : Option JoinSite) (c : StmtConfig scfg)
    (d : Nat) (t e : List Statement) : Nat :=
  let exitsT := blockAlwaysExits [] t
  let exitsE := blockAlwaysExits [] e
  if !exitsT && !exitsE then d else
  let covered (ls : List String) :=
    (!exitsT || Block.checkExitsCoveredByBlocks ls t) &&
    (!exitsE || Block.checkExitsCoveredByBlocks ls e)
  let bs := enclosingBlocks c
  let site := match (List.range bs.length).find? (fun i => covered ((bs.take (i + 1)).map (·.1)))
    with
    | some i => (bs[i]?.map (·.2)).getD d
    | none => d
  match head with
  | some (.depth h) => if site < h then d else site
  | _ => site

/-- Structured configurations: `stepInterp` steps; a fork at an `if` joins where its branches
    first meet: the end of the `if`, or, when a branch always exits, the end of the labelled
    block that catches its `exit`s (`ifJoinDepth`); a path leaves the branches without reaching
    the join by an `exit` past the join. -/
def structuredShape (scfg : ExploreCfg) : ProcBodyShape scfg (StmtConfig scfg) :=
  letI := symLang scfg
  { step := fun fuel c =>
      letI := forkEffects scfg
      stepInterp (symStepCmd scfg) fuel c
    ended := fun
      | .terminal _ => some .finished
      | .exiting l _ => some (.unmatchedExit l)
      | _ => none
    forkSite := fun head c => match deepest c with
      | .stmt (.ite _ t e _) _ => some (.depth (ifJoinDepth head c (wrapperDepth c) t e))
      | _ => none
    atJoin := fun
      | .depth d, c => stmtAtJoin d c
      | _, _ => false
    passedJoin := fun
      | .depth d, c => wrapperDepth c ≤ d && !stmtAtJoin d c
      | _, _ => false
    joinEnv := fun c => match deepest c with
      | .terminal e => some e
      | _ => none
    setJoinEnv := fun c e => replaceDeepest c (.terminal e)
    forMerge := fun _ e => e
    deadObls := deadBranchObls
    declares := fun c => match deepest c with
      | .stmt (.cmd cmd) _ => initDecl? cmd
      | _ => none }

/-! ## CFG configurations -/

/-- The engine's configurations for CFGs of Core commands under `symLang scfg`. -/
abbrev BlockConfig (scfg : ExploreCfg) : Type :=
  @ICFGConfig String Command Expression (symLang scfg)

/-- The locals declared in the blocks of `decls` (each block's label with the variables it
    declares) that no block dominating block `j` declares, given the dominators `dom`
    (`computeDominators`). A local declared both in a block that dominates `j` and in one that
    does not is still in scope at `j`. -/
private def localsOutOfScope (dom : CFG.Dom.DomMap)
    (decls : List (String × List CoreIdent)) (j : String) : List CoreIdent :=
  if decls.isEmpty then [] else
  let kept : Std.HashSet CoreIdent :=
    .ofList (decls.flatMap fun p => bif CFG.Dom.dominates dom p.1 j then p.2 else [])
  decls.flatMap fun p =>
    bif CFG.Dom.dominates dom p.1 j then [] else p.2.filter (!kept.contains ·)

/-- Where the branches of a fork to `t` and `e` first meet: with `R` the blocks both reach
    (each counting as reaching itself), the one block of `R` none of whose predecessors (`preds`)
    is in `R`; `none` if `R` has no such block or several. A path from `t` or `e` may bypass
    it. `succs` and `preds` are the CFG's
    successor and predecessor maps, `n` its number of blocks. -/
private def firstCommonBlock (succs preds : Std.HashMap String (List String)) (n : Nat)
    (t e : String) : Option String :=
  let reach (l : String) := (CFG.reachableSetFromSuccsWith succs n l).insert l
  let rt := reach t
  let r := (reach e).toList.filter rt.contains
  let rs : Std.HashSet String := .ofList r
  match r.filter fun x => (preds.getD x []).all (!rs.contains ·) with
  | [x] => some x
  | _ => none

/-- Whether `g` has no cycle reachable from its entry. -/
private def cfgAcyclic (g : Core.DetCFG) : Bool :=
  (CFG.cycleLabelsWith g.succMap [g.entry]).isEmpty

/-- Per block `j` of `g`, the blocks that reach `j` (`j` included), each set computed at its
    first use. -/
private def cfgReachTo (g : Core.DetCFG) : Std.HashMap String (Thunk (Std.HashSet String)) :=
  g.blocks.foldl (fun m (j, _) => m.insert j
    (Thunk.mk fun _ => (CFG.reachableSetFromSuccsWith g.predMap g.blocks.length j).insert j)) {}

/-- Whether block `l` reaches block `j`, by the reach-to sets `reachTo` (`cfgReachTo`); if
    `reachTo` has no set for `j`, only `j` reaches it. -/
private def reachesIn (reachTo : Std.HashMap String (Thunk (Std.HashSet String))) (l j : String) :
    Bool :=
  match reachTo[j]? with
  | some r => r.get.contains l
  | none => l == j

/-- The join of a fork whose branches meet at block `x` before nesting, given the path's
    innermost open join `head?`: block `x`, unless the flag `acyclic` is set, the innermost open
    join is at block `h`, and `reaches x h` is false; then block `h`. -/
private def nestJoin (reaches : String → String → Bool) (acyclic : Bool) (head? : Option JoinSite)
    (x : String) : JoinSite :=
  match head? with
  | some (.block h) => if acyclic && !reaches x h then .block h else .block x
  | _ => .block x

/-- CFG configurations of the CFG `g`: `stepInterpCFG` steps. Where a fork at the end of block
    `B`, with successors `t` and `e`, joins:

    * In an acyclic CFG, at the one block of those both `t` and `e` reach that has no
      predecessor among them (`firstCommonBlock`; a path from `t` or `e` may bypass it), or, if
      there is no single such block, at `B`'s immediate post-dominator (`computePostIdoms`).
      A join never lies outside the path's innermost open join: if the chosen block neither is
      that join's block nor reaches it, the fork joins at that join's block instead, so each
      open join's block reaches the next one's. A path has left a fork's branches when its
      block cannot reach the join's block.
    * In a CFG with a cycle, at `B`'s immediate post-dominator; a path leaves the branches only
      by ending.
    * A fork for which neither rule gives a block opens no join.

    At a merge at block `J`, each branch leaves out the locals that no block dominating `J`
    declares (`computeDominators`): the CFG type checker (`CFG.typeCheck`) scopes each local to
    the blocks its declaring block dominates and refuses a declaration on a cycle, so no step
    from `J` on reads them. -/
def cfgShape (scfg : ExploreCfg) (g : Core.DetCFG) : ProcBodyShape scfg (BlockConfig scfg) :=
  letI := symLang scfg
  let ipdoms := g.computePostIdoms
  let dom := g.computeDominators
  let decls := (g.blocks.map fun (d, b) => (d, WF.blockInitVars b)).filter (!·.2.isEmpty)
  -- Per block, the locals a merge there leaves out, computed at the first merge there.
  let outAt : Std.HashMap String (Thunk (List CoreIdent)) := g.blocks.foldl
    (fun m (j, _) => m.insert j (Thunk.mk fun _ => localsOutOfScope dom decls j)) {}
  let succs := g.succMap
  let preds := g.predMap
  let n := g.blocks.length
  let acyclic := cfgAcyclic g
  let reaches := reachesIn (cfgReachTo g)
  -- Per forking block, the join its fork opens before nesting, computed at its first fork.
  let joinAt : Std.HashMap String (Thunk (Option String)) := g.blocks.foldl
    (fun m (b, blk) => match blk.transfer with
      | .condGoto _ t e _ => m.insert b (Thunk.mk fun _ =>
          if acyclic then
            match firstCommonBlock succs preds n t e with
            | some x => some x
            | none => (ipdoms.get? b).join
          else (ipdoms.get? b).join)
      | .finish _ => m) {}
  { step := fun fuel c =>
      letI := forkEffects scfg
      stepInterpCFG (m := ForkM) (StepCmdM.toStore (symStepCmd scfg)) fuel c
    ended := fun
      | .terminal _ => some .finished
      | _ => none
    forkSite := fun
      | head, .inBlock _ l [] (.condGoto ..) _ =>
        (joinAt[l]?.map (·.get)).join.map (nestJoin reaches acyclic head)
      | _, _ => none
    atJoin := fun
      | .block j, .atBlock _ l _ => l == j
      | _, _ => false
    passedJoin := fun
      | .block j, .atBlock _ l _ | .block j, .inBlock _ l .. => acyclic && !reaches l j
      | _, _ => false
    joinEnv := fun
      | .atBlock _ _ e | .terminal e => some e
      | _ => none
    setJoinEnv := fun
      | .atBlock g' l _, e => .atBlock g' l e
      | .terminal _, e => .terminal e
      | c, _ => c
    forMerge := fun
      | .block j, e =>
        let out := match outAt[j]? with
          | some out => out.get
          | none => localsOutOfScope dom decls j
        { e with store := e.store.drop out }
      | _, e => e
    deadObls := fun _ _ _ => []
    declares := fun
      | .inBlock _ _ (cmd :: _) _ _ => initDecl? cmd
      | _ => none }

/-! ## Merging -/

/-- The record of choices (`PathState.choices`, newest first) of the path that merges the
    branches of fork `j` (`ma` the then-branch's record, `mb` the else-branch's): the entries
    before the fork, then, if either branch added entries after it, one `merge` with the fork's
    guard and each branch's added entries, oldest first. -/
def mergeChoices (j : Join) (ma mb : List Choice) : List Choice :=
  let added (m : List Choice) := (m.take (m.length - j.baseChoices)).reverse
  let base := ma.drop (ma.length - j.baseChoices)
  match added ma, added mb with
  | [], [] => base
  | ta, tb => .merge j.guard ta tb :: base

/-- Whether `ng` is `negate g`, comparing `g` by pointer first (`ptrFastEq`) instead of
    building `negate g`. -/
private def isNegationOf (ng g : Expression.Expr) : Bool :=
  match ng with
  | .ite m c t e =>
    ptrFastEq c g && ptrFastEq m symExecLoc && ptrFastEq t Core.false && ptrFastEq e Core.true
  | _ => false

/-- Whether the path conditions of the two branches of fork `j` still have the form merging
    relies on (`mergeEnvs_pc`): the then-branch's ends in `(_, j.guard) :: base` and the
    else-branch's in `(_, negate j.guard) :: base`, with one `base` of length `j.basePcLen` (at
    a join the explorer opened, the fork's path condition). The length test on `base` also
    rejects a path condition shorter than `j.basePcLen + 1`, which `drop` would keep whole. Both
    bases are normally one list, so `ptrFastEq` usually decides them by pointer identity.

    The engine's steps only add entries at the front of a path condition (`forkEffects`), so this
    holds at every join the explorer opens. A step that changed an entry already there, even to
    an equivalent one, would make it fail: the two branches then continue as separate paths,
    each with its own path condition, so merging is lost but no result changes. -/
private def mergeShapeOk (j : Join) (sa sb : PathState) : Bool :=
  match sa.pc.drop (sa.pc.length - (j.basePcLen + 1)),
      sb.pc.drop (sb.pc.length - (j.basePcLen + 1)) with
  | (_, ga) :: ba, (_, gb) :: bb =>
    ba.length == j.basePcLen && ptrFastEq ga j.guard && isNegationOf gb j.guard &&
      ptrFastEq ba bb
  | _, _ => false

/-- The symbol the path-condition entry `(l, e)` defines when it is a join symbol's definition
    (`nameJoinStep`): its label is a join definition's (`isJoinValueLabel`), its condition is
    `s == v` for a join symbol `s` (`isJoinValueName`), and `s` is not in `defined`, the join
    symbols the entries before it on the path define. An entry of that form for a symbol already
    defined is an assumption about it. -/
def joinDefSym? (defined : Std.HashSet String) (l : String) (e : Expression.Expr) :
    Option String :=
  if isJoinValueLabel l then
    match e with
    | .eq _ (.fvar _ s _) _ =>
      if isJoinValueName s.name && !defined.contains s.name then some s.name else none
    | _ => none
  else none

/-- `defined` and the join symbols the entries of `pc` (newest first) define (`joinDefSym?`),
    oldest first. -/
def joinDefsOf (pc : List (String × Expression.Expr)) (defined : Std.HashSet String := {}) :
    Std.HashSet String :=
  pc.foldr (fun (l, e) acc => match joinDefSym? acc l e with
    | some s => acc.insert s
    | none => acc) defined

/-- A branch's own path-condition entries `own` (newest first) as the merged path condition
    holds them: each under the fork's guard (`wrap`), except a join symbol's definition
    (`joinDefSym?`, with `defined` the join symbols the entries before them define), which is
    kept as it is. -/
-- TODO: prove that keeping a definition unguarded keeps the merged path condition's meaning:
-- its symbol is fresh in its branch, so every model of the other branch's path condition
-- extends, giving the symbol its definition's value, to one of the definition.
def mergeOwn (wrap : Expression.Expr → Expression.Expr) (defined : Std.HashSet String)
    (own : List (String × Expression.Expr)) : List (String × Expression.Expr) :=
  (go own).2
where
  /-- `mergeOwn` on `own`, with the join symbols `own` and `defined` define. -/
  go : List (String × Expression.Expr) → Std.HashSet String × List (String × Expression.Expr)
    | [] => (defined, [])
    | (l, e) :: older =>
      let (d, out) := go older
      match joinDefSym? d l e with
      | some s => (d.insert s, (l, e) :: out)
      | none => (d, (l, wrap e) :: out)

/-- Merge the environments `ea` (then-branch, path state `sa`) and `eb` (else-branch, path
    state `sb`) of the two branches of fork `j` at its join: values that differ, ignoring source
    locations (`LExpr.beqIgnoringMetadata`), become `if g then va else vb`; the path condition
    is the shared prefix, then each branch's entries added after the fork's guard, keeping their
    labels: a join symbol's definition as it is, any other entry guarded by `g` (then-branch
    `if g then e else true`, else-branch `if g then true else e`; `mergeOwn`); the record of
    choices keeps both branches' (`mergeChoices`). Returns the merged environment and path state, and the differing
    variables with their merged values, in the store's key order. `none` if the branches bind
    different variables, or if their path conditions do not have the form `mergeShapeOk` checks. -/
def mergeEnvs {scfg : ExploreCfg} (j : Join) (ea eb : @IEnv Expression (symLang scfg))
    (sa sb : PathState) :
    Option (@IEnv Expression (symLang scfg) × PathState × List (CoreIdent × Expression.Expr)) :=
  letI := symLang scfg
  if sa.pc.length < j.basePcLen + 1 || sb.pc.length < j.basePcLen + 1 || !mergeShapeOk j sa sb
  then none else
  let wa : StoreWrites := ea.store.writes
  let wb : StoreWrites := eb.store.writes
  let keys := (wa.keys ++ wb.keys).eraseDups
  let diffs? : Option (List (CoreIdent × Expression.Expr)) := keys.foldlM (fun acc k =>
    match ea.store.get k, eb.store.get k with
    | some va, some vb =>
      some (if va.beqIgnoringMetadata vb then acc else acc ++ [(k, .ite symExecLoc j.guard va vb)])
    | none, none => some acc
    | _, _ => none) []
  match diffs? with
  | none => none
  | some diffs =>
    let store := diffs.foldl (fun σ (k, v) => σ.update k v) ea.store
    let own (pc : List (String × Expression.Expr)) := (pc.take (pc.length - j.basePcLen)).dropLast
    let base := sa.pc.drop (sa.pc.length - j.basePcLen)
    let defined := joinDefsOf base
    let pc := mergeOwn (LExpr.ite symExecLoc j.guard Core.true ·) defined (own sb.pc) ++
      mergeOwn (LExpr.ite symExecLoc j.guard · Core.true) defined (own sa.pc) ++ base
    some ({ ea with store },
          { sa with pc := pc, segment := [], merged := true,
                    choices := mergeChoices j sa.choices sb.choices, next := max sa.next sb.next },
          diffs)

/-- The label of the path-condition entry defining the symbol a join gives variable `x`. -/
def joinValueLabel (x : CoreIdent) : String := s!"<join_value: {x.name}>"

/-- The type annotation of a symbol, if `e` is an annotated free variable. -/
def symType? : Expression.Expr → Option LMonoTy
  | .fvar _ _ ty => ty
  | _ => none

/-- The state `nameJoinValues` threads through a join's merged values: the store, the path
    condition, the symbol counter, the number of values left unnamed for want of a type, and
    the values named so far with their symbols. -/
abbrev NameAcc (scfg : ExploreCfg) : Type :=
  @IStore Expression (symLang scfg) × List (String × Expression.Expr) × Nat × Nat ×
    List (Expression.Expr × Expression.Expr)

/-- One step of `nameJoinValues` for variable `x` with merged value `v`, where `ta` and `tb` are
    the declared types the then- and else-branch recorded (`PathState.types`):
    * a variable either branch recorded with a type containing a function type keeps `v` (an
      equation between functions is not something the solver decides, and the verifier never
      asks for a function's value);
    * a variable both branches recorded with the same type `ty`, whose value equals, up to
      source locations, one named earlier at this join by a symbol of type `ty`, gets that
      symbol;
    * any other variable both branches recorded with the same type `ty` gets the symbol
      `s := mkSym scfg.joinPre k ty x`, and the path condition the entry `s == v` (labelled
      `joinValueLabel x`); the counter moves on;
    * otherwise (no type recorded, or the branches disagree) `x` keeps `v`, and the step counts
      it as unnamed. -/
def nameJoinStep {scfg : ExploreCfg} (ta tb : Std.TreeMap CoreIdent LMonoTy identCmp)
    (acc : NameAcc scfg) (xv : CoreIdent × Expression.Expr) : NameAcc scfg :=
  letI := symLang scfg
  let (σ, pc, k, unnamed, named) := acc
  let (x, v) := xv
  let isFun (t? : Option LMonoTy) : Bool := (t?.map LMonoTy.containsArrow).getD false
  if isFun ta[x]? || isFun tb[x]? then acc else
  match ta[x]?, tb[x]? with
  | some ty, some ty' =>
    if ty == ty' then
      match named.find? (fun p => p.1.beqIgnoringMetadata v && symType? p.2 == some ty) with
      | some (_, s) => (σ.update x s, pc, k, unnamed, named)
      | none =>
        let s := mkSym scfg.joinPre k ty x.name
        (σ.update x s, (joinValueLabel x, LExpr.eq symExecLoc s v) :: pc, k + 1, unnamed,
          (v, s) :: named)
    else (σ, pc, k, unnamed + 1, named)
  | _, _ => (σ, pc, k, unnamed + 1, named)

/-- Name the merged values `diffs` of a join (`mergeEnvs`) by fresh symbols (`nameJoinStep`,
    counting from `next`, with the declared types `ta` and `tb` the then- and else-branch
    recorded): each variable `x` with merged value `v` and a recorded type gets a symbol `s`,
    and the path condition gets the entry `s == v`. Later expressions mention `s`, so the
    obligations write each merged value once, in its definition, and nested joins nest symbols.
    Join symbols have their own prefix (`ExploreCfg.joinPre`) and their own counter
    (`DState.joinNext`); `next` must be the explorer's join counter, so that no other join used
    any number counted here. Also returns how many values
    were left unnamed for want of a type, and the counter after the symbols used. -/
-- TODO: prove that naming preserves meaning: every model of the path condition before naming
-- extends, giving each join symbol its definition's value, to a model of the named one, under
-- which the named store denotes what the unnamed one does.
def nameJoinValues {scfg : ExploreCfg} (next : Nat) (ta tb : Std.TreeMap CoreIdent LMonoTy identCmp)
    (diffs : List (CoreIdent × Expression.Expr))
    (env : @IEnv Expression (symLang scfg)) (st : PathState) :
    @IEnv Expression (symLang scfg) × PathState × Nat × Nat :=
  letI := symLang scfg
  let r := diffs.foldl (nameJoinStep (scfg := scfg) ta tb) (env.store, st.pc, next, 0, [])
  ({ env with store := r.1 }, { st with pc := r.2.1 }, r.2.2.2.1, r.2.2.1)

/-- Merge the two branches of fork `j` at its join (`a` the then-branch, `b` the else-branch):
    the environments each brings to the merge (`ProcBodyShape.forMerge`) merged by `mergeEnvs`,
    with the merged values named by fresh symbols counted from the join counter `joinNext`
    (`nameJoinValues`), at the then-branch's configuration. Also returns the number of
    differing variables, the number left unnamed, and the join counter after the merge. `none`
    if a branch is not at a join, or `mergeEnvs` refuses. -/
def mergeBranches {scfg : ExploreCfg} {C : Type} (sh : ProcBodyShape scfg C) (j : Join)
    (joinNext : Nat) (a b : Entry C) :
    Option (Entry C × Nat × Nat × Nat) :=
  match sh.joinEnv a.cfg, sh.joinEnv b.cfg with
  | some ea, some eb =>
    match mergeEnvs j (sh.forMerge j.site ea) (sh.forMerge j.site eb) a.st b.st with
    | some (env, st, ds) =>
      let named := nameJoinValues joinNext a.st.types b.st.types ds env st
      some ({ cfg := sh.setJoinEnv a.cfg named.1, st := named.2.1, node := a.node,
              budget := min a.budget b.budget, joins := a.joins.drop 1 },
            ds.length, named.2.2.1, named.2.2.2)
    | none => none
  | _, _ => none

/-! ## Exploring -/

/-- The explorer's state. A path inside a fork's branches is one whose `joins` still lists that
    fork. -/
structure DState (C : Type) where
  work : List (Entry C)
  nodes : Array Node
  steps : Nat := 0
  next : Nat
  dead : Array Obl := #[]
  /-- Per fork: how many paths are still inside its branches (running, or waiting at the
      join). -/
  inBranches : Array Nat := #[]
  /-- Per fork: the paths waiting at its join. -/
  waiting : Array (List (Entry C)) := #[]
  /-- How many paths wait at joins: the total length of the lists in `waiting`. -/
  waitingCount : Nat := 0
  finished : Nat := 0
  merges : Nat := 0
  /-- Merged values left unnamed at joins (`Result.joinValuesUnnamed`). -/
  joinValuesUnnamed : Nat := 0
  /-- The next number for a join symbol (`nameJoinValues`); a counter of its own, apart from
      `next`. -/
  joinNext : Nat := 0
  /-- The checks some path reached (`checkOf`): for each label, the metadata of the checks with
      that label. -/
  reached : Std.HashMap String (Array (MetaData Expression)) := {}

mutual
/-- Place a path that just stepped: make it wait at its innermost open join if it arrived
    there, drop that join if it left the branch another way, else put it on the worklist. `n`
    bounds the depth of joins left to place: every path waiting at a fork has that fork's join
    on top of the same enclosing joins, and each nested `joinBranchesF` places entries with one
    join fewer, so `e.joins.length` suffices. At `0` the entry goes on the worklist as is (its
    forks are then not merged); `place` passes `e.joins.length + 1`. -/
private def placeF {scfg : ExploreCfg} {C : Type} (sh : ProcBodyShape scfg C) (pol : MergePolicy)
    (proc : String) (n : Nat) (s : DState C) (e : Entry C) : DState C :=
  match e.joins, n with
  | [], _ | _, 0 => { s with work := e :: s.work }
  | j :: js, n + 1 =>
    if sh.atJoin j.site e.cfg then
      joinBranchesF sh pol proc (n + 1)
        { s with waiting := s.waiting.modify j.fork (· ++ [e]),
                 waitingCount := s.waitingCount + 1 } j.fork
    else if sh.passedJoin j.site e.cfg then
      let s := joinBranchesF sh pol proc (n + 1)
        { s with inBranches := s.inBranches.modify j.fork (· - 1) } j.fork
      placeF sh pol proc n s { e with joins := js }
    else { s with work := e :: s.work }
  termination_by 2 * n + 1
  decreasing_by all_goals (try simp only [wfParam]) <;> omega

/-- When every path still inside fork `f`'s branches waits at its join: merge the two branches
    (if the policy agrees and they are mergeable), else let the waiting paths continue
    separately. `n` bounds the joins of those paths; at `0` they go back on the worklist
    unmerged. -/
private def joinBranchesF {scfg : ExploreCfg} {C : Type} (sh : ProcBodyShape scfg C)
    (pol : MergePolicy) (proc : String) (n : Nat) (s : DState C) (f : Nat) : DState C :=
  let ps := s.waiting[f]?.getD []
  let inside := s.inBranches[f]?.getD 0
  if ps.isEmpty || ps.length != inside then s else
  let s := { s with waiting := s.waiting.set! f [], waitingCount := s.waitingCount - ps.length,
                    inBranches := s.inBranches.set! f 0 }
  match n with
  | 0 => ps.foldl (fun s p => { s with work := { p with joins := p.joins.drop 1 } :: s.work }) s
  | n + 1 =>
  let release (s : DState C) : DState C :=
    ps.foldl (fun s p => placeF sh pol proc n s { p with joins := p.joins.drop 1 }) s
  match ps with
  | [p, q] =>
    match p.joins.head?, q.joins.head? with
    | some jp, some jq =>
      let (a, b) := if jp.side then (p, q) else (q, p)
      if jp.side == jq.side then release s else
      let merged := Thunk.mk fun _ => mergeBranches sh jp s.joinNext a b
      -- `s.waitingCount` excludes `ps`: their fork's entry is cleared above.
      let view : JoinView := { proc, depth := a.joins.length - 1,
                               pending := s.work.length + s.waitingCount,
                               finished := s.finished,
                               differing := Thunk.mk fun _ => (merged.get.map (·.2.1)).getD 0 }
      if !pol view then release s else
      match merged.get with
      | none => release s
      | some (m, _, unnamed, joinNext) =>
        let i := s.nodes.size
        let nodes := s.nodes.push { parent := none, cond := none, startPc := m.st.pc }
        let nodes := setStatus (setStatus nodes a.node .joined) b.node .joined
        let nodes := nodes.modify jp.node fun n => { n with cont := some i }
        -- The merged path counts once, not twice, inside every enclosing fork's branches.
        let inBranches := m.joins.foldl (fun l j => l.modify j.fork (· - 1)) s.inBranches
        placeF sh pol proc n { s with nodes, inBranches, merges := s.merges + 1,
                                      joinValuesUnnamed := s.joinValuesUnnamed + unnamed,
                                      joinNext }
          { m with node := i }
    | _, _ => release s
  | _ => release s
  termination_by 2 * n
  decreasing_by all_goals (try simp only [wfParam]) <;> omega
end

/-- `placeF` with enough fuel for the entry's joins. -/
private def place {scfg : ExploreCfg} {C : Type} (sh : ProcBodyShape scfg C) (pol : MergePolicy)
    (proc : String) (s : DState C) (e : Entry C) : DState C :=
  placeF sh pol proc (e.joins.length + 1) s e

/-- A path ended (finished, stopped, out of budget or work, unmatched exit): it no longer counts
    toward any open join. -/
private def endPath {scfg : ExploreCfg} {C : Type} (sh : ProcBodyShape scfg C) (pol : MergePolicy)
    (proc : String) (s : DState C) (e : Entry C) (st : NodeStatus) : DState C :=
  let s := { s with nodes := setStatus s.nodes e.node st,
                    finished := s.finished + (match st with | .finished => 1 | _ => 0) }
  e.joins.foldl (fun s j =>
    joinBranchesF sh pol proc (e.joins.length + 1)
      { s with inBranches := s.inBranches.modify j.fork (· - 1) } j.fork) s

/-- The run's result from the explorer's state. `unreached` holds the obligations of the checks
    skipped at a decided guard (`ProcBodyShape.deadObls`) that no path reached; the checks of
    the body no path reached at all are added by `Result.addUnreached`. -/
private def done {C : Type} (s : DState C) : Result :=
  let notReached (o : Obl) := !checkReached s.reached (checkOf o)
  { nodes := s.nodes, steps := s.steps, unreached := s.dead.toList.filter notReached,
    reached := s.reached, merges := s.merges, joinValuesUnnamed := s.joinValuesUnnamed }

/-- `r` with the obligations of the checks in `checks` that no path of the run reached and
    `r.unreached` does not already hold, in the order of `checks`. A run that is not complete
    says nothing about them, so it adds none. -/
def Result.addUnreached (r : Result) (checks : List Obl) : Result :=
  match r.completeness with
  | .complete =>
    let seen := r.unreached.foldl (fun cs u => addCheck cs (checkOf u)) r.reached
    { r with unreached := r.unreached ++ checks.filter (fun o => !checkReached seen (checkOf o)) }
  | .notAnalyzed _ => r

/-- Give every pending or waiting path its final status when the run stops early: the status
    `ProcBodyShape.ended` gives (`finished`, or `unmatchedExit` if exiting) if it has ended, else
    `status` (`outOfWork` when the work bound runs out, `overPathLimit` at the path limit). -/
private def markUnfinished {scfg : ExploreCfg} {C : Type} (sh : ProcBodyShape scfg C) (s : DState C)
    (status : NodeStatus := .outOfWork) : DState C :=
  let pending := s.work ++ s.waiting.toList.flatten
  let nodes := pending.foldl (fun ns e => setStatus ns e.node ((sh.ended e.cfg).getD status))
    s.nodes
  { s with nodes }

/-- Whether the run has more paths than `ExploreCfg.maxPaths` allows: finished ones plus those still
    to be explored (on the worklist or waiting at a join). -/
def overPathLimit {scfg : ExploreCfg} {C : Type} (s : DState C) : Bool :=
  match scfg.maxPaths with
  | some n => s.finished + s.work.length + s.waitingCount > n
  | none => false

/-- Whether no path waits at any join. -/
private def noneWaiting {C : Type} (s : DState C) : Bool :=
  s.waiting.toList.flatten.isEmpty

/-- Put every waiting path back on the worklist, unmerged and with no open joins (with correct
    counts in `inBranches` no path is left waiting once the worklist is empty). -/
private def releaseWaiting {C : Type} (s : DState C) : DState C :=
  s.waiting.toList.flatten.foldl (fun s p => { s with work := { p with joins := [] } :: s.work })
    { s with waiting := s.waiting.map (fun _ => []), waitingCount := 0 }

/-- Count a step's outcomes inside the forks `e` descends from, and, if the step at `e`'s
    configuration forked into two continuing paths and the fork has a join
    (`ProcBodyShape.forkSite`), open a join for its branches; returns the joins of the outcome on
    each side (`true` for the then-branch). Every outcome inherits `e`'s joins, so each
    enclosing fork counts the outcomes beyond the first, whether or not the step opens a join.
    -/
private def openJoin {scfg : ExploreCfg} {C : Type} (sh : ProcBodyShape scfg C) (s : DState C)
    (e : Entry C) (outs : Outcomes C) : DState C × (Bool → List Join) :=
  let okCount := outs.countP fun (o, _) => match o with | .ok _ => true | _ => false
  let inBranches := e.joins.foldl (fun l j => l.modify j.fork (· + (outs.length - 1)))
    s.inBranches
  let s := { s with inBranches }
  -- A join opens only at a fork whose two paths a merge could accept (`mergeShapeOk`): each
  -- side's path condition is the entry's with one entry added, the guard `g` on the
  -- then-branch and `negate g` on the else-branch. At any other fork no join opens, so its paths
  -- never wait for each other. Each tail is normally the entry's list itself, so `ptrFastEq`
  -- usually decides it by pointer identity.
  let shaped? : Option Expression.Expr := match outs with
    | [(_, sa), (_, sb)] =>
      match sa.pc, sb.pc with
      | (_, g) :: ta, (_, ng) :: tb =>
        if ptrFastEq ta e.st.pc && ptrFastEq tb e.st.pc && isNegationOf ng g then some g
        else none
      | _, _ => none
    | _ => none
  if okCount != 2 then (s, fun _ => e.joins) else
  match shaped?, sh.forkSite (e.joins.head?.map (·.site)) e.cfg with
  | some thenGuard, some site =>
    let f := s.inBranches.size
    ({ s with inBranches := s.inBranches.push 2, waiting := s.waiting.push [] }, fun side =>
      { fork := f, site, side, node := e.node,
        guard := thenGuard, basePcLen := e.st.pc.length,
        baseChoices := e.st.choices.length } :: e.joins)
  | _, _ => (s, fun _ => e.joins)

/-- Put a step's outcomes in the tree: one outcome stays in the entry's node, several become
    new children of it; returns each outcome with its node and side (`true` for the first). -/
private def placeInTree {C : Type} (nodes : Array Node) (e : Entry C) (outs : Outcomes C) :
    Array Node × List (Out C × PathState × Nat × Bool) :=
  match outs with
  | [(o, st)] => (addObls nodes e.node st.segment, [(o, st, e.node, true)])
  | _ =>
    let nodes := setStatus nodes e.node .forked
    outs.zipIdx.foldl (fun (ns, ts) ((o, st), k) =>
      let i := ns.size
      let ns := ns.push { parent := some e.node, cond := st.pc.head?.map (·.2), startPc := st.pc }
      (addObls ns i st.segment, ts ++ [(o, st, i, k == 0)])) (nodes, [])

/-- Whether a path that stepped to state `st` is infeasible: the newest entry of its path
    condition is literal `false`. Then no run follows the path and it ends (`infeasible`, with the
    entry's label); obligations recorded in the step stay on it. `none` otherwise, in constant
    time. A step adds at most one entry; an older `false` would have ended the path at the step
    that added it. A condition that contradicts others without being literal `false` is left to
    the solver. `_before`, the path condition the step started from, is not needed. -/
def infeasibleStatus (_before : List (String × Expression.Expr))
    (st : PathState) : Option NodeStatus :=
  match st.pc with
  | (label, c) :: _ => if LExpr.isFalse _ c then some (.infeasible label) else none
  | [] => none

/-- Continue one outcome of `e`'s step at node `i` with step budget `b` and open joins `joins`:
    `place` it if it continues, `endPath` it if it stopped or is infeasible
    (`infeasibleStatus`). -/
private def placeOutcome {scfg : ExploreCfg} {C : Type} (sh : ProcBodyShape scfg C)
    (pol : MergePolicy)
    (proc : String) (s : DState C) (e : Entry C) (b : Nat) (joins : List Join) (o : Out C)
    (st : PathState) (i : Nat) : DState C :=
  match o with
  | .ok c' =>
    match infeasibleStatus e.st.pc st with
    | some status => endPath sh pol proc s { e with node := i, joins } status
    | none => place sh pol proc s { cfg := c', st := { st with segment := [] }, node := i,
                                     budget := b, joins }
  | .stop r => endPath sh pol proc s { e with node := i, joins } (.stopped r)

/-- Advance one path: end it if it has ended (`ProcBodyShape.ended`) or is out of budget; else
    take one engine step in `ForkM` (`ProcBodyShape.step`), record the checks it reaches (their
    obligations' positions, which it then removes) and the obligations of checks it skips, open
    a join at a two-way fork, put the outcomes in the tree, and place or end each one. -/
private def stepPath {scfg : ExploreCfg} {C : Type} (sh : ProcBodyShape scfg C) (pol : MergePolicy)
    (proc : String) (s : DState C) (e : Entry C) : DState C :=
  match sh.ended e.cfg with
  | some status => endPath sh pol proc s e status
  | none =>
    match e.budget with
    | 0 => endPath sh pol proc s e (.stopped .replayFuelExhausted)
    | b + 1 =>
      let types := match sh.declares e.cfg with
        | some (x, ty) => e.st.types.insert x ty
        | none => e.st.types
      let st0 := { e.st with segment := [], next := s.next, types }
      let outs := sh.step (b + 1) e.cfg scfg st0
      -- A step with no outcome leaves the rest of the path unexplored: the path stops, which
      -- makes the run incomplete (`NodeStatus.incompleteReason?`).
      if outs.isEmpty then
        endPath sh pol proc s e (.stopped (.interrupted "a step had no outcome"))
      else
      let next := outs.foldl (fun n (_, st) => max n st.next) s.next
      let reached := outs.foldl (fun r (_, st) =>
        st.segment.foldl (fun r o => addCheck r (checkOf o)) r) s.reached
      let s := { s with next, steps := s.steps + 1, reached,
                        dead := s.dead ++ sh.deadObls e.cfg outs e.st.pc }
      let (s, mkJoin) := openJoin sh s e outs
      let (nodes, targets) := placeInTree s.nodes e outs
      targets.foldr (fun (o, st, i, side) s =>
        placeOutcome sh pol proc s e b (mkJoin side) o st i) { s with nodes }

/-- Explore depth-first: advance the first path on the worklist (`stepPath`) until none is
    left, merging the branches of a fork at its join when the policy says so. `maxSteps` bounds
    the number of pops; paths still pending then are `outOfWork` (or the status
    `ProcBodyShape.ended` gives, if they have ended). Once more paths exist than
    `scfg.maxPaths` allows (`overPathLimit`), the paths still pending are `overPathLimit`
    instead. The fresh-symbol counter is the explorer's, so names are unique across the whole
    tree. The result records the checks some path reached (`Result.reached`), so a caller that
    has the body can add the ones no path reached (`Result.addUnreached`). -/
def explore {scfg : ExploreCfg} {C : Type} (sh : ProcBodyShape scfg C) (maxSteps : Nat)
    (start : Entry C) (pol : MergePolicy := .never) (proc : String := "") : Result :=
  let rec go : Nat → DState C → Result
    | 0,        s => done (markUnfinished sh s)
    | fuel + 1, s =>
      if overPathLimit (scfg := scfg) s then done (markUnfinished sh s .overPathLimit)
      else
      match s.work with
      | []        => if noneWaiting s then done s else go fuel (releaseWaiting s)
      | e :: rest => go fuel (stepPath sh pol proc { s with work := rest } e)
  go maxSteps { work := [start], nodes := #[{ parent := none, cond := none }],
                next := start.st.next }

/-! ## Procedures -/

/-- Every name a procedure mentions: formals, their `old` names, and the names its body
    declares or assigns (`HasVarsImp` of `Procedure.Body`) and the procedure reads
    (`Procedure.getVars`: the contract's free variables and what the body reads, including a
    CFG body's branch conditions). -/
private def procNames (p : Procedure) : List String :=
  let formals := (p.header.inputs.keys ++ p.header.outputs.keys).map (·.name)
  formals ++ formals.map (fun x => (CoreIdent.mkOld x).name) ++
    (HasVarsImp.definedVars (P := Expression) p.body false ++
      HasVarsImp.modifiedVars (P := Expression) p.body ++ Procedure.getVars p).map (·.name)

/-- The CFG a run of a CFG body `g` executes: a new entry block running `pre` (the
    precondition assumes) and jumping to `g`'s entry, `g`'s blocks with every `finish` replaced
    by a jump to a new exit block, and that exit block, running `post` (the checked
    postcondition asserts) and finishing. The new labels are not labels, branch targets or the
    entry of `g`, nor each other (`Strata.Name.freshName` over the keys of `predMap` and `g`'s
    entry). -/
private def wrapCFG (g : Core.DetCFG) (pre post : List Command) : Core.DetCFG :=
  let used : Std.HashSet String := (Std.HashSet.ofList g.predMap.keys).insert g.entry
  let entry := Strata.Name.freshName used "$__symexec_entry"
  let exit := Strata.Name.freshName (used.insert entry) "$__symexec_exit"
  let blocks : List (String × DetBlock String Command Expression) := g.blocks.map fun (l, b) =>
    (l, match b.transfer with
      | .finish md => { b with transfer := .goto exit md }
      | .condGoto .. => b)
  { entry,
    blocks := (entry, { cmds := pre, transfer := .goto g.entry }) :: blocks ++
      [(exit, { cmds := post, transfer := .finish #[] })] }

/-- Set up a procedure: choose a symbol prefix no name of the procedure starts with; bind every
    input and output to a fresh symbol of its declared type; bind `old x` to `x`'s entry symbol
    for in-out parameters. Then run, for a structured body, `precondition assumes ++ body ++
    postcondition asserts`, for a CFG body, the CFG with an entry block assuming the
    preconditions and an exit block asserting the postconditions (`wrapCFG`). A free
    postcondition is not checked: it becomes `assume true` (`Imperative.Check.asserts`). An
    abstract procedure has no body to check against its contract, so its result is empty.

    Assumes what the pipeline establishes before VC generation (`symExecRequires`): no calls,
    no nondeterministic guards, monomorphic procedures, type-annotated expressions.  A
    violation is not refused here; it stops its path (a call: `interrupted`; a nondeterministic
    guard: `expectedBooleanChoice`); a polymorphic procedure is not detected: its formals get
    symbols of their type-variable types.  Loops (structured loops, and cycles in a CFG body)
    are unrolled up to the run budget; a path that runs out of it stops, and the run is not
    complete.

    The caller passes the factory; for SMT-encodable obligations it should be the program's
    factory with `inline` functions removed (`Core.Simplify.withoutInline`). -/
def exploreProc (cfg : ExploreCfg) (maxSteps runFuel : Nat) (F : Lambda.Factory CoreLParams)
    (p : Procedure) (extraNames : List String := []) (tag : String := "")
    (pol : MergePolicy := .never) : Result :=
  -- `tag` extends the chosen prefix (still a prefix no name starts with), so callers can keep
  -- symbols of different procedures apart; `extraNames` are further names to avoid (e.g. the
  -- factory's functions).
  let names := extraNames ++ procNames p
  let cfg := { cfg with pre := choosePrefix names ++ tag,
                        joinPre := choosePrefix names defaultJoinPrefix ++ tag }
  letI := symLang cfg
  -- An in-out parameter is bound once (its input symbol).
  let formals := p.header.inputs.toList ++
    p.header.outputs.toList.filter (fun (x, _) => !p.header.inputs.keys.contains x)
  let (σ, n) := formals.foldl (fun (σ, n) (x, ty) =>
    (σ.update x (mkSym cfg.pre n ty x.name), n + 1)) (IStore.ofStore (fun _ => none), 0)
  let σ := p.header.inputs.keys.foldl (fun σ x =>
    if p.header.outputs.keys.contains x then
      match σ.get x with
      | some v => σ.update (CoreIdent.mkOld x.name) v
      | none => σ
    else σ) σ
  let pre : List (Imperative.Cmd Expression) := Imperative.Check.assumes p.spec.preconditions
  let post : List (Imperative.Cmd Expression) := Imperative.Check.asserts p.spec.postconditions
  let env : IEnv Expression := { store := σ, factory := F }
  -- The declared types of the formals and their `old` names (`PathState.types`).
  let types : Std.TreeMap CoreIdent LMonoTy identCmp := formals.foldl (fun t (x, ty) =>
    (t.insert x ty).insert (CoreIdent.mkOld x.name) ty) {}
  let names := formals.map (·.1) ++ formals.map (fun (x, _) => CoreIdent.mkOld x.name)
  let entry := names.filterMap fun x => (σ.get x).map (x, ·)
  match p.body with
  | .structured body _ =>
    let stmt (c : Imperative.Cmd Expression) : Statement := .cmd (.cmd c)
    let stmts := pre.map stmt ++ body ++ post.map stmt
    let r := explore (structuredShape cfg) maxSteps
      { cfg := .stmts stmts env, st := { next := n, types }, node := 0, budget := runFuel }
      pol p.header.name.name
    { r.addUnreached (stmtCheckObls stmts) with entry, stmts }
  | .cfg g _ =>
    let g := wrapCFG g (pre.map CmdExt.cmd) (post.map CmdExt.cmd)
    let r := explore (cfgShape cfg g) maxSteps
      { cfg := .atBlock g g.entry env, st := { next := n, types }, node := 0, budget := runFuel }
      pol p.header.name.name
    { r.addUnreached (blockCheckObls g) with entry, graph := some g }
  -- An abstract procedure has no body to explore: its result is empty. The program-level folds
  -- skip abstract procedures, so they do not reach this arm.
  | .abstract => { nodes := #[], steps := 0, entry }

/-! ## Programs -/

/-- The program facts symbolic execution requires: `noCalls`, `noLoops`, `noNondetGuards`,
    `exitsCovered`, `noPolymorphicProcedures`, `typeAnnotated` (symbols need monomorphic
    types; `typeOf` reads type annotations) and `noCFGCycles`. All are established by the
    passes before VC generation. CFG bodies are accepted (`exploreProc`) once their loops are
    cut (`cfgLoopElim`). -/
def symExecRequires : List ProgramFact :=
  [.noCalls, .noLoops, .noNondetGuards, .exitsCovered, .noPolymorphicProcedures, .typeAnnotated,
   .noCFGCycles]

/-- The required facts a program fails, among those with an executable check (`typeAnnotated`
    has none; it is trusted, as in the pipeline). -/
def failedRequires (prog : Program) : List ProgramFact :=
  symExecRequires.filter fun f =>
    match f.check? with
    | some chk => !chk prog
    | none => false

/-- Symbolically execute every procedure of a program, after checking `symExecRequires`
    (`.error` names the facts that fail): the entry point of symbolic execution for
    verification, hence its name. Symbols avoid the factory's function names as well
    as each procedure's names. -/
def symExecProgram (cfg : ExploreCfg) (maxSteps runFuel : Nat) (F : Lambda.Factory CoreLParams)
    (prog : Program) : Except (List ProgramFact) (List (String × Result)) :=
  let fnNames := F.toArray.toList.map (·.name.name)
  match failedRequires prog with
  | [] => .ok <| prog.decls.filterMap fun
    | .proc p _ =>
      -- An abstract procedure has no body to check, and call elimination has removed every
      -- call to it, so it is skipped.
      if p.body.isAbstract then none
      else some (p.header.name.name, exploreProc cfg maxSteps runFuel F p fnNames)
    | _ => none
  | fs => .error fs

end -- public section

end Core.SymExec
