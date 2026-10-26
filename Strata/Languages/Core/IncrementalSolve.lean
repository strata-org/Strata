/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Verifier
public import Std.Sync.Mutex
import Strata.Languages.Core.ObligationExtraction
import Strata.Transform.CommonSubexprElim

/-! # Walking a verification tree with long-lived solver sessions

A session wraps a live solver together with the encoder state that names its terms,
and assertions are checked by walking a tree, each solver keeping the context of the
branch it is on.

Three pieces.

`Session` holds a live solver's state and the `AbstractEncoderState` naming terms
for *that* solver, plus how much of a path it has been sent. `Session.tell` sends
facts and keeps them; `Session.check` tests a goal and changes nothing, by passing
the goal to `check-sat-assuming`, which leaves the solver's assertions as they were.

`VTree` is read off the program's statements. A passified body already is a tree:
this reads the statements `ObligationExtraction` reads and keeps their shape.

`run` opens up to *n* sessions and runs them concurrently. Which goals each one checks,
and in which order, is fixed before any starts by `planSessions`, from the tree and *n*
alone: a session checks a run of consecutive goals in tree order, so a goal's verdict
does not depend on which solver finished first. Each goal belongs to one session, which
is what keeps it proved once by one solver.

Facts are asserted unguarded here, so a session can only extend a path it already
holds. Moving to a path that diverges means rebuilding the context, which is
counted and reported. Guarding a branch arm's assumptions would let one solver serve
both arms without rebuilding; this module asserts them unguarded.

## Where this sits

`Core.verifyPipeline` runs the transform pipeline and then, inside its `vcDischarge`
phase, calls a `CoreSMTSolver`; `Core.verify` passes it `coreSMTSolver` below under
`--incremental`:

```
verifyPipeline → runTransforms (… nondetElim, symbolicEval, betaReduce, commonSubexprElim)
                 → oblProgram
                 → coreSMTSolver factory oblProgram   -- solver.getD mkDefaultCoreSMTSolver
                 → VCResults
```

`mkDefaultCoreSMTSolver` is `verifySingleEnv`, which calls `buildEnv`, then
`ObligationExtraction.extractObligations`, then loops over the obligations calling
a `DischargeFn` for each. `verifyProgram` below replaces both of those: it reads the
same program `extractObligations` would have read, keeps its tree, and walks that.

It returns `VCResults` and `Statistics`, which is what that seam expects. The shaping
`getObligationResult` does around a per-obligation discharge is split between the two sides.
Check-mode masking happens here, before the check, because what the mask decides is which
questions a goal is asked. Model extraction happens here too, inside the
session that produced the model, because an `EncoderState` does not outlive the session that
built it. Phase model validation happens at the seam, in `verifyPipeline`, which knows the phases.

## How assertions become work

Nothing is encoded before the walk. What runs first only prepares the way, and none
of it touches SMT:

1. `readProgram` walks the declarations and statements and returns a `VTree`: one
   node per run of facts, holding those facts once and the assertions checked after
   them, with the arms of a tail `if *` as children. The assertions of one branch
   stay together because they were written together.
2. `layoutOf` numbers the nodes in pre-order and records, for each, its goals, its
   children. A goal's path holds the nodes' own arrays of facts, so a session appends
   the runs it has not walked yet.

The tree, the layout and the plan are immutable and shared read-only. The mutable state is
two `Std.Mutex` cells: the schedule below, holding each goal's outcome once it is known, and
the record of the solvers a run has started, which it closes at the end.

Encoding then happens inside the workers, in parallel: `Session.prove` advances
that session's own `SMTEncodeState`, which discovers the sorts, functions and
axioms its assertion mentions, declares the ones this solver has not been declared,
sends the facts it has not been sent, and asks the question. Two workers on
different arms encode different things and never wait for each other; two workers
on the same arm each encode its facts once and reuse them for every assertion
below.

`planSessions` is where the goals are divided among the workers, and states the rule.
-/

namespace Core.IncrementalSolve

open Std (Format format)
open Strata Strata.SMT Strata.SMT.Encoder
open Imperative (PathConditionEntry)

public section

/-- The names of a program's axioms, in declaration order. -/
def axiomNamesOf (p : Program) : List String :=
  p.decls.filterMap fun d => d.getAxiom?.map (·.name)

/-- The error `readDecls` reports for a function that still carries a precondition, wherever it
    is declared. Nothing here generates an obligation for the precondition, yet the encoder emits
    total `SafeDiv`, `SafeMod` and safe bitvector operations assuming it was checked.
    `ObligationExtraction` reports the same error. -/
private def preconditionError (name : Expression.Ident) : String :=
  s!"IncrementalSolve: function '{name}' still carries a precondition; \
    run precondition elimination first"

/-! ## Reading the tree

A node holds one run of facts, however many statements that is, and the assertions that
follow it. A fact appearing after an assertion closes the node and continues as its only
child, which is what keeps an assumption from applying to an assertion written before it. -/

/-- What a node claims: an assertion, with its label, property and metadata. The context it is
    claimed under is the facts on the path to its node. -/
structure Goal where
  label : String
  property : Imperative.PropertyType
  expr : Expression.Expr
  md : Imperative.MetaData Expression

/-- A node is one run of facts and every assertion that sees exactly those facts.

    Each fact is held once, by its node. A goal carries only its claim, and its context is
    the concatenation of `facts` along the root-to-node path, which a session accumulates
    by walking, so goals below a node share what the node holds.

    Several assertions share a node when nothing separates them, because they then
    see the same facts and a session holding the node can check any of them without
    being told anything more. What starts a new node is a fact *after* an assertion,
    since the assertions before it must not see it. So the four shapes are: a leaf,
    with goals and no children; a chain link, with goals and one child, which is that
    case; an arm split, with no goals and one child per arm of a tail `if *`; and both
    at once, when an `if *` directly follows assertions. -/
structure VTree where
  facts : Array (PathConditionEntry Expression)
  goals : Array Goal
  children : Array VTree
  deriving Inhabited

/-- The number of goals in this subtree. -/
def VTree.goalCount : VTree → Nat
  | ⟨_, goals, children⟩ =>
    children.attach.foldl (fun acc ⟨c, _⟩ => acc + c.goalCount) goals.size

/-- Read a procedure's body into a tree, for `readDecls`, which hangs the result off the point
    the procedure is declared at. `facts` and `goals` are those of the node
    being read, which a fact after a goal closes: the rest of the body then goes in a child. -/
private partial def readStmts (facts : Array (PathConditionEntry Expression))
    (goals : Array Goal) (ss : Statements) : Except String VTree :=
  match ss with
  | [] => .ok { facts, goals, children := #[] }
  | s :: rest =>
    -- A fact before any goal joins this node; one after a goal starts a child, so the goals
    -- above it are checked without it.
    let fact (entry : PathConditionEntry Expression) : Except String VTree :=
      if goals.isEmpty then readStmts (facts.push entry) goals rest
      else do
        let child ← readStmts #[entry] #[] rest
        .ok { facts, goals, children := #[child] }
    match s with
    | .cmd (.cmd (.assert label e md)) =>
      readStmts facts
        (goals.push { label, property := Imperative.convertMetaDataPropertyType md,
                      expr := e, md }) rest
    | .cmd (.cmd (.cover label e md)) =>
      readStmts facts (goals.push { label, property := .cover, expr := e, md }) rest
    | .cmd (.cmd (.assume label e _md)) => fact (.assumption label e)
    | .cmd (.cmd (.init name ty e _md)) => fact (.varDecl name ty e)
    | .ite .nondet thenSs elseSs _md => do
      let t ← readStmts #[] #[] thenSs
      let f ← readStmts #[] #[] elseSs
      -- Nothing follows an `if *` in a passified body, but the extractor accepts it,
      -- so a continuation is read as one more child: it sees neither arm's facts.
      let after ← if rest.isEmpty then pure (#[] : Array VTree)
        else do let r ← readStmts #[] #[] rest; pure #[r]
      .ok { facts, goals, children := #[t, f] ++ after }
    -- Anything else, a statement-level type declaration included, is refused, as
    -- `extractObligations` refuses it: the tree reads exactly the programs that path reads.
    | _ => .error "IncrementalSolve: unsupported statement in a passive body"

/-- Read the declarations as a chain, for `readProgram`, hanging each procedure off the point it was
    declared at. A procedure sees the axioms and `distinct` groups declared before it
    and no others, which is what `ObligationExtraction` accumulates as it walks. That
    prefix is a chain of ancestors, so procedures sharing a prelude share the nodes
    holding it. -/
private partial def readDecls (funcNames : List String)
    (facts : Array (PathConditionEntry Expression))
    (goals : Array Goal) (kids : Array VTree) (ds : List Decl) : Except String VTree :=
  -- What follows a goal or a child is read below it, so a node's facts precede its goals and
  -- its children, and everything after keeps the declaration order.
  let below (facts' : Array (PathConditionEntry Expression)) (goals' : Array Goal)
      (rest : List Decl) : Except String VTree := do
    let t ← readDecls funcNames facts' goals' #[] rest
    .ok { facts, goals, children := kids.push t }
  let global (entry : PathConditionEntry Expression) (rest : List Decl) :
      Except String VTree :=
    if kids.isEmpty && goals.isEmpty then readDecls funcNames (facts.push entry) goals kids rest
    else below #[entry] #[] rest
  let definition (rest : List Decl) : Except String VTree :=
    if kids.isEmpty && goals.isEmpty then readDecls funcNames facts goals kids rest
    else below #[] #[] rest
  match ds with
  | [] => .ok { facts, goals, children := kids }
  | d :: rest =>
    match d with
    | .ax a _ => global (.assumption a.name a.e) rest
    | .distinct name es _ => global (.distinct (toString name) es) rest
    -- Read from the statements `extractObligations` reads, so a parameter named like a
    -- function is renamed apart here too and a procedure with a contract is refused.
    | .proc proc _ => do
      let t ← readStmts #[] #[] (← ObligationExtraction.procedureStatements funcNames proc)
      readDecls funcNames facts goals (kids.push t) rest
    -- A function reaches a solver as a definition when a term mentions it. Goals declared
    -- after it are read in a child, so a solver holding its definition never checks a goal
    -- declared before it: a definition need not be a conservative extension (a recursive one,
    -- for instance), and a goal must not be checked under one it could not see.
    | .func f _ =>
      if f.preconditions.isEmpty then definition rest
      else .error (preconditionError f.name)
    | .recFuncBlock funcs _ =>
      match funcs.find? (fun f => !f.preconditions.isEmpty) with
      | some f => .error (preconditionError f.name)
      | none => definition rest
    -- A lemma is a goal checked under the declarations before it and never assumed, so it is a
    -- goal of the node it is declared at. The lemmas of one program therefore share a context:
    -- those declared one after another are goals of one node, and one after an axiom or a
    -- function is a goal of the child that declaration opens, which extends the context of the
    -- lemmas before it.
    | .lemma l md =>
      let goal : Goal := { label := toString l.name,
                           property := Imperative.convertMetaDataPropertyType md,
                           expr := l.e, md }
      if kids.isEmpty then readDecls funcNames facts (goals.push goal) kids rest
      else below #[] #[goal] rest
    | _ => readDecls funcNames facts goals kids rest

/-- Read a program as one tree. Every verdict of this back end rests on the tree holding exactly
    the obligations `extractObligations` finds, each under the same assumptions in the same order.
    That agreement is tested, not proved: `sameObligations` in the tests compares the two on every
    test program. -/
def readProgram (p : Program) : Except String VTree :=
  readDecls (ObligationExtraction.programFuncNames p) #[] #[] #[] p.decls

/-- A position in the tree, as the child indices taken from the root. -/
abbrev Pos := Array Nat

/-- One unit of work: an assertion, where it sits, and the runs of facts on the way
    there, outermost first. The arrays in `path` are the nodes' own: what a session
    appends when it descends is `path.drop (levels it already holds)`. -/
structure WorkItem where
  id : Nat
  pos : Pos
  path : Array (Array (PathConditionEntry Expression))
  goal : Goal
  /-- Labels of the axioms on the path that irrelevant-axiom removal drops for this goal. They are
      decided by the goal alone, before any solver starts, so they do not depend on which worker
      proves the goal. -/
  pruned : List String := []
  /-- The set of axioms on the path that this goal keeps, stored as a number for speed: the
      program's axioms are numbered once, and axiom `i` is in the set when bit `i` is set. Then
      `held &&& keptAxioms == held` says the goal keeps every axiom in `held`, in one step however
      many axioms the program has. -/
  keptAxioms : Nat := 0
  /-- CSE definitions on the path that this goal does not use and that the solver must not be
      sent, because their text cannot be written for it. Empty except on the path the
      per-obligation discharge also isolates, see `pruneUnusedCSEDefinitions`. -/
  skippedDefs : Std.HashSet String := {}

/-- The tree laid out for the walk. Nodes, and so goals, are numbered in pre-order, which is
    the order a solver walking the tree depth-first checks them in. All of it is immutable and
    shared by every solver. -/
structure Layout where
  /-- One entry per goal, indexed by goal number. -/
  tasks : Array WorkItem
  /-- The goals on each node, by node number. -/
  goalIds : Array (Array Nat)
  /-- The children of each node, by node number. -/
  children : Array (Array Nat)

private structure Build where
  tasks : Array WorkItem := #[]
  goalIds : Array (Array Nat) := #[]
  children : Array (Array Nat) := #[]

/-- For `layoutOf`: number the nodes in pre-order, collecting each one's goals and children, and
    building one `WorkItem` per goal. -/
private partial def buildLayout (t : VTree) (pos : Pos)
    (path : Array (Array (PathConditionEntry Expression))) (b : Build) : Build :=
  let me := b.goalIds.size
  let path := path.push t.facts
  let b := { b with goalIds := b.goalIds.push #[], children := b.children.push #[] }
  let (tasks, ids) := t.goals.foldl (init := (b.tasks, (#[] : Array Nat))) fun acc g =>
    let (ts, ids) := acc
    let id := ts.size
    (ts.push { id, pos, path, goal := g }, ids.push id)
  let b := { b with tasks, goalIds := b.goalIds.setIfInBounds me ids }
  (List.range t.children.size).foldl (init := b) fun b i =>
    match t.children[i]? with
    | none => b
    | some c =>
      let kid := b.goalIds.size
      let b := { b with
        children := b.children.setIfInBounds me ((b.children.getD me #[]).push kid) }
      buildLayout c (pos.push i) path b

/-- Lay the tree out for the walk. -/
def layoutOf (t : VTree) : Layout :=
  let b := buildLayout t #[] #[] {}
  { tasks := b.tasks, goalIds := b.goalIds, children := b.children }

/-- The index of the first element of `xs` that `size` ranks largest, by its first component and
    then its second, among those whose first component is at least 2, or `none` when there is
    none. -/
private def firstLargest (xs : Array (Array Nat)) (size : Array Nat → Nat × Nat) : Option Nat :=
  (List.range xs.size).foldl (init := none) fun best i =>
    let (n, m) := size (xs.getD i #[])
    if n < 2 then best else
    match best with
    | some b =>
      let (bn, bm) := size (xs.getD b #[])
      if n > bn || (n == bn && m > bm) then some i else some b
    | none => some i

/-- Replace `xs[i]` with its two halves, the first one holding the larger half when its size is
    odd. -/
private def halve (xs : Array (Array Nat)) (i : Nat) : Array (Array Nat) :=
  let x := xs.getD i #[]
  let k := (x.size + 1) / 2
  xs.extract 0 i ++ #[x.extract 0 k, x.extract k x.size] ++ xs.extract (i + 1) xs.size

/-- Split the goals into sessions, each a list of goals in tree order that one solver checks in that
    order from a fresh start. The split is decided here, from the tree and `n` alone, before any
    solver starts, so which goals a solver checks, and in which order, is the same on every run,
    however many solvers run at once: a goal's verdict cannot depend on which solver finished first.
    It balances the sessions greedily, first at the granularity of nodes, then of goals.

    1. Every leaf starts a session. Then, in turns, each session in leaf order takes the parent of
       the topmost node it holds, unless another session has taken it, until no session can go
       higher. A session is so a chain of nodes from some node down to its leaf, which one solver
       walks without starting again, after sending the path above its topmost node; every node
       belongs to exactly one session; and the nodes shared by many leaves go to the sessions below
       them in turn. Nodes holding no goal are left out, and a session
       left without a goal is dropped.
    2. With at least `n` sessions, that is the plan.
    3. While there are fewer than `n` sessions, the first session holding the most nodes, and of
       those the most goals, is cut into two chains of almost as many nodes, the upper one first.
       With `byNode` this goes on, whatever `n` is, until every session holds one node.
    4. Without `byNode`, while there are still fewer than `n` sessions, the first session holding
       the most goals, now one node's goals or a share of them, is cut into two of almost as many
       goals.

    There are never more sessions than goals. A session that does not start at the root starts by
    sending the path to its first goal. -/
def planSessions (l : Layout) (n : Nat) (byNode : Bool := false) : Array (Array Nat) := Id.run do
  let nodes := l.goalIds.size
  if l.tasks.size == 0 then return #[]
  let parent : Array (Option Nat) := (List.range nodes).foldl (init := Array.replicate nodes none)
    fun acc u => (l.children.getD u #[]).foldl (fun a k => a.setIfInBounds k (some u)) acc
  let leaves := (List.range nodes).toArray.filter fun u => (l.children.getD u #[]).isEmpty
  -- Step 1.
  let mut taken : Array Bool := leaves.foldl (fun a u => a.setIfInBounds u true)
    (Array.replicate nodes false)
  let mut chains : Array (Array Nat) := leaves.map (#[·])
  let mut climbing := true
  while climbing do
    climbing := false
    for j in [0 : chains.size] do
      match (chains.getD j #[]).back? >>= (parent.getD · none) with
      | some p =>
        if !taken.getD p true then
          taken := taken.setIfInBounds p true
          chains := chains.modify j (·.push p)
          climbing := true
      | none => pure ()
  -- Top down, keeping only the nodes that hold goals.
  let mut sessions : Array (Array Nat) := (chains.map fun c =>
    c.reverse.filter fun u => !(l.goalIds.getD u #[]).isEmpty).filter (!·.isEmpty)
  -- Step 3.
  let goalsIn := fun (c : Array Nat) => c.foldl (fun a u => a + (l.goalIds.getD u #[]).size) 0
  while byNode || sessions.size < n do
    match firstLargest sessions fun c => (c.size, goalsIn c) with
    | some i => sessions := halve sessions i
    | none => break
  -- Step 4.
  let mut goals : Array (Array Nat) := sessions.map (·.flatMap (l.goalIds.getD · #[]))
  while !byNode && goals.size < n do
    match firstLargest goals fun c => (c.size, 0) with
    | some i => goals := halve goals i
    | none => break
  return goals

/-- A solver whose operations can fail with a structured error of their own, presented in `IO`
    with that error raised as an `IO.Error`. Sound because `ExceptT` over `IO` carries no state:
    nothing a call does is held anywhere but in the solver itself, so no update can be lost
    across a callback that re-enters it. `mkForall` and `mkExists` take callbacks that already
    run in `IO`, so those are lifted into the solver's monad. -/
def raisingIn {τ σ ε : Type} [ToString ε] (s : AbstractSolver τ σ (ExceptT ε IO))
    (failed : IO.Ref (Option String)) : AbstractSolver τ σ IO :=
  let r {α : Type} (x : ExceptT ε IO α) : IO α := do
    match ← x.run with
    | .ok a => pure a
    | .error e =>
      -- Recorded before it is raised, so the caller can tell this failure, which belongs to the
      -- term being written, from one of the solver process itself.
      failed.set (some (toString e))
      throw (IO.userError (toString e))
  { setLogic := fun l => r (s.setLogic l), setOption := fun n v => r (s.setOption n v),
    comment := fun c => r (s.comment c),
    boolSort := r s.boolSort, intSort := r s.intSort, realSort := r s.realSort,
    stringSort := r s.stringSort, regexSort := r s.regexSort,
    bitvecSort := fun n => r (s.bitvecSort n), arraySort := fun k v => r (s.arraySort k v),
    constrSort := fun n a => r (s.constrSort n a),
    mkBool := fun b => r (s.mkBool b), mkInt := fun i => r (s.mkInt i),
    mkPrim := fun p => r (s.mkPrim p), mkAppOp := fun o a t => r (s.mkAppOp o a t),
    mkAnd := fun ts => r (s.mkAnd ts), mkOr := fun ts => r (s.mkOr ts),
    mkNot := fun t => r (s.mkNot t), mkImplies := fun a b => r (s.mkImplies a b),
    mkAdd := fun ts => r (s.mkAdd ts), mkSub := fun ts => r (s.mkSub ts),
    mkMul := fun ts => r (s.mkMul ts), mkDiv := fun a b => r (s.mkDiv a b),
    mkMod := fun a b => r (s.mkMod a b), mkNeg := fun t => r (s.mkNeg t),
    mkAbs := fun t => r (s.mkAbs t),
    mkEq := fun ts => r (s.mkEq ts), mkLt := fun ts => r (s.mkLt ts),
    mkLe := fun ts => r (s.mkLe ts), mkGt := fun ts => r (s.mkGt ts),
    mkGe := fun ts => r (s.mkGe ts),
    mkIte := fun c t e => r (s.mkIte c t e),
    mkSelect := fun a i => r (s.mkSelect a i), mkStore := fun a i v => r (s.mkStore a i v),
    mkApp := fun f a => r (s.mkApp f a),
    mkForall := fun bs cb => r (s.mkForall bs fun ts => liftM (cb ts)),
    mkExists := fun bs cb => r (s.mkExists bs fun ts => liftM (cb ts)),
    declareNew := fun n t => r (s.declareNew n t),
    mkParam := fun n t => r (s.mkParam n t),
    declareFun := fun n a t => r (s.declareFun n a t),
    defineFun := fun n a t b => r (s.defineFun n a t b),
    defineFunRec := fun n a t b => r (s.defineFunRec n a t b),
    declareSort := fun n k => r (s.declareSort n k),
    declareDatatype := fun n ps cb => r (s.declareDatatype n ps cb),
    declareDatatypes := fun ds cb => r (s.declareDatatypes ds cb),
    assert := fun t => r (s.assert t), checkSat := r s.checkSat,
    checkSatAssuming := fun ts => r (s.checkSatAssuming ts),
    getUnsatAssumptions := r s.getUnsatAssumptions, getModel := r s.getModel,
    getModelText := fun ts => r (s.getModelText ts), getValue := fun ts => r (s.getValue ts),
    termToSMTLibString := fun t => r (s.termToSMTLibString t),
    reset := r s.reset, close := r s.close }

/-! ## Sessions -/

/-- A live solver and everything it has been told.

    Both halves of the encoding live here: `core` is the Core-level
    fold that turns path conditions into terms and grows the `SMT.Context` as it
    discovers functions and axioms, and `enc` holds the SMT-LIB names and handles
    for *this* solver. A worker therefore encodes what it needs itself, as it walks,
    and nothing has to be encoded in advance for everybody.

    The counters are what make sending incremental: `decl*` is how much of the
    context this solver has been declared, `told*` how much of the path it has been
    asserted. -/
structure Session (τ σ : Type) where
  name : Nat
  /-- The solver, spoken to only through `AbstractSolver`, so the scheduler names no
      backend. A backend keeps whatever state it needs behind its own handle and presents
      itself in `IO`. -/
  solver : AbstractSolver τ σ IO
  /-- Set when a call failed because a term or type could not be written for this solver, so
      the failure is kept to the goal that caused it and the run carries on, as the
      per-obligation path keeps it to its obligation. -/
  encodingFailure : IO.Ref (Option String)
  enc : AbstractEncoderState τ
  core : SMTEncodeState
  /-- What this solver has been declared, by identity. The context a goal is encoded against is
      a fork that is not written back, so two goals on one node produce sibling lists of
      symbols; each symbol is therefore sent the first time a goal needs it. -/
  declSorts : Std.HashSet String := {}
  declUfs : Std.HashSet String := {}
  declIfs : Std.HashSet String := {}
  declAxms : Std.HashSet Term := {}
  declDatatypes : Std.HashSet String := {}
  /-- Names that are program variables, declared when the walk reaches them rather
      than with the context. -/
  managed : Std.HashSet String := {}
  /-- Assumptions this solver has been sent, by identity. With pruning, two goals on one path
      may keep different axioms, so each assumption is sent the first time a goal keeps it. -/
  toldAssums : Std.HashSet Term := {}
  /-- The set of axioms this solver holds, stored as a number as `WorkItem.keptAxioms` is. Each
      goal adds its kept axioms with `|||`. A goal that keeps every one of them is asked exactly
      the per-obligation question. Any other goal sees the extra axioms under lazy pruning, and
      under exact pruning the solver resets before it. -/
  heldAxioms : Nat := 0
  /-- How many of the path's variable declarations and definitions this solver has been sent.
      A count is sound here: the walk only appends entries to
      the fold's single frame and goes back up only through a reset, so a session's `varDecls`
      and `varDefs` grow as one prefix in path order, and a goal's own fork adds to neither. -/
  toldDecls : Nat := 0
  toldDefs : Nat := 0
  /-- How many levels of a path this session has been sent. -/
  heldLevels : Nat := 0
  /-- The node the session last proved a goal on, as child indices from the root. While
      `heldLevels` is positive, the session holds exactly the path to it. -/
  heldPos : Pos := #[]
  checks : Nat := 0
  /-- Contexts built: one when the session opens, one per rebuild after that. -/
  contexts : Nat := 0
  /-- Goals this solver checked while holding an axiom their own pruning drops, whatever their
      verdict: under lazy pruning, how many goals were asked something other than the
      per-obligation question. -/
  goalsWithExtraAxioms : Nat := 0
  /-- Nanoseconds spent inside the solver's checks, so a run can separate time spent solving
      from time spent encoding and sending what the solver is told. -/
  solveNanos : Nat := 0
  /-- Checks this solver has answered since it was started, whatever contexts it was given. A
      failure on a solver that has answered some is put down to the solver, so the goal is
      asked again on a new one. -/
  answered : Nat := 0
  /-- The solver failed and no replacement could be started, so the next goal starts by trying
      to replace it again. -/
  dead : Bool := false
  /-- The `set-option`s this solver was opened with, kept because `(reset)` clears them and
      a rebuild has to send them again. Held on the session so a rebuild does not need the
      options that produced them. -/
  preludeOptions : Array (String × String) := #[]

/-- Run an encoder action against this session's solver, threading both states. The `Session`
    functions talk to the solver through it. -/
private def onSolver {α τ σ : Type} (s : Session τ σ)
    (act : AbstractSolver τ σ IO → AbstractEncoderM τ IO α) : IO (α × Session τ σ) := do
  let (a, enc) ← (act s.solver).run s.enc
  return (a, { s with enc := enc })

/-- Set the logic and send the session's options, for `Session.open` and `Session.rebuild`.
    Everything else about the context is
    discovered by the walk, so a worker starts solving without waiting for anyone to encode
    the program for it. Both opening and rebuilding go through here, because `(reset)` leaves
    a solver needing exactly what a fresh one needs. -/
private def Session.startContext {τ σ : Type} (s : Session τ σ) :
    IO (Session τ σ) := do
  let (_, s) ← onSolver s fun solver => liftM (solver.setLogic "ALL")
  s.preludeOptions.foldlM (init := s) fun s (name, value) => do
    let (_, s) ← onSolver s fun solver => liftM (solver.setOption name value)
    return s

/-- Open a session on a fresh solver. The backend decides what a solver is; the session
    only ever speaks to it through `AbstractSolver`. -/
def Session.open {τ σ : Type} (name : Nat) (solver : AbstractSolver τ σ IO)
    (encodingFailure : IO.Ref (Option String))
    (preludeOptions : Array (String × String)) (ctx0 : SMT.Context) :
    IO (Session τ σ) := do
  let s : Session τ σ :=
    { name, solver, encodingFailure,
      -- Seeded with the names the context has already had declared, so a UF encoded later
      -- cannot be sanitized onto a sort, datatype, constructor or selector name the solver
      -- already knows. Datatypes and sorts reach the solver directly, so this is how the
      -- encoder's `usedNames` learns about them.
      enc := { base := EncoderState.initWithNames ctx0.preDeclaredNames },
      core := .init { ctx := ctx0 }, contexts := 1, preludeOptions }
  -- The solver is already running, and a session that never returns is never closed, so a
  -- failure setting it up closes it here.
  try s.startContext
  catch e =>
    try solver.close catch _ => pure ()
    throw e

def Session.close {τ σ : Type} (s : Session τ σ) : IO Unit := do
  s.solver.close

/-- Throw away what a solver holds and start it again, empty. Used when a session
    is sent to a path that diverges from the one it holds, which unguarded facts
    cannot be moved off. Everything it had learned about the context goes too, so
    this is the expensive move. -/
def Session.rebuild {τ σ : Type} (s : Session τ σ) (ctx0 : SMT.Context) :
    IO (Session τ σ) := do
  let (_, s) ← onSolver s fun solver => liftM solver.reset
  let s : Session τ σ :=
    { name := s.name, solver := s.solver, encodingFailure := s.encodingFailure,
      enc := { base := EncoderState.initWithNames ctx0.preDeclaredNames },
      core := .init { ctx := ctx0 },
      checks := s.checks, contexts := s.contexts + 1,
      goalsWithExtraAxioms := s.goalsWithExtraAxioms, solveNanos := s.solveNanos,
      preludeOptions := s.preludeOptions,
      answered := s.answered }
  s.startContext

/-- The prefix that marks the failure of a walk that could start no solver at all, so a caller
    can tell it apart from any other failure and fall back to the per-obligation path. -/
private def noSolverStarted : String := "incremental: no solver could be started: "

/-- Start a solver for `run` and `Session.respawn`, trying again twice, after 1 s and then 2 s,
    if starting it fails. A remote
    service may refuse a session for a moment, under throttling for instance, and a refusal that
    ended the worker would cost every goal it had not reached. -/
private def spawnPatiently {τ σ : Type}
    (spawn : IO.Ref (Option String) → IO (AbstractSolver τ σ IO))
    (failed : IO.Ref (Option String)) :
    IO (AbstractSolver τ σ IO) :=
  go 2 1000
where
  -- Each wait is the delay plus up to half of it again at random, so solvers started together
  -- do not all try again at the same moment.
  go : Nat → UInt32 → IO (AbstractSolver τ σ IO)
    | 0, _ => spawn failed
    | n + 1, delay => try spawn failed catch _ => do
        IO.sleep (delay + (← IO.rand 0 (delay.toNat / 2)).toUInt32)
        go n (delay * 2)

/-- Replace a solver that failed with a new process, empty. A dead process cannot be reset, so
    this is what follows a failure the session cannot attribute to a term it could not write.
    The counters carry over, so the run's statistics still cover the whole worker. A `patient`
    replacement waits out a brief refusal; otherwise starting it is tried once. -/
def Session.respawn {τ σ : Type} (s : Session τ σ)
    (spawn : IO.Ref (Option String) → IO (AbstractSolver τ σ IO)) (ctx0 : SMT.Context)
    (patient : Bool := true) :
    IO (Session τ σ) := do
  try s.close catch _ => pure ()
  let solver ← if patient then spawnPatiently spawn s.encodingFailure else spawn s.encodingFailure
  let fresh ← Session.open s.name solver s.encodingFailure s.preludeOptions ctx0
  return { fresh with checks := s.checks, contexts := s.contexts + 1,
                      goalsWithExtraAxioms := s.goalsWithExtraAxioms, solveNanos := s.solveNanos }

/-- Turn a solver verdict and the counterexample text that came with it into the `SMT.Result`
    the rest of the pipeline reports.

    The model is parsed with `parseModelDDM` and mapped back to program variables with
    `processModel`, the same two steps the per-obligation path uses, so a counterexample obtained
    from a long-lived session is textually the one obtained from a one-shot solve. That mapping
    needs the encoder state, which is why this is done where the check happened.

    A model that fails to parse or to map leaves the refutation without a model: the verdict is
    the solver's and stands on its own, and `sat` with an empty model still reports a
    refutation. -/
def resultOfDecision (ctx : SMT.Context) (vars : List (Expression.Ident × Expression.Ty))
    (estate : EncoderState) : Decision × String → IO Core.SMT.Result
  | (.unsat, _) => return .unsat
  | (.timeout, _) => return .err "timeout"
  | (.sat, modelText) => return .sat (← parse modelText)
  -- An `unknown` keeps whatever model came with it, as on the per-obligation path, so that a
  -- phase able to validate the model can still promote it to `sat`.
  | (.unknown, modelText) => do
    let model ← parse modelText
    return if model.isEmpty then .unknown none else .unknown (some model)
where
  parse (modelText : String) : IO (Imperative.SMT.Model Expression.Ident) := do
    if modelText.isEmpty then return []
    let raw ← Imperative.SMT.parseModelDDM modelText estate.usedNames
    -- Matched as `processModel` matches, except that the variables with no value are skipped.
    let values := Imperative.SMT.modelValues raw
    return vars.filterMap fun (v, ty) =>
      match Imperative.SMT.getSMTId (Core.SMT.typedVarToSMTFn ctx) v ty estate with
      | .ok id => values[id]?.map (v, ·)
      | .error _ => none

/-- The obligation a goal stands for, in the shape every other back end reports. The path is
    the assumptions: `PathConditions` is a list of runs, which is what `WorkItem.path` already
    is. -/
def obligationOf (item : WorkItem) : Imperative.ProofObligation Expression :=
  { label := item.goal.label, property := item.goal.property,
    -- One frame, oldest fact first, which is the shape `extractObligations` gives an obligation.
    assumptions := [item.path.toList.flatMap (·.toList)],
    obligation := item.goal.expr, metadata := item.goal.md }

/-- Encode one assertion against this session's own state, send whatever that
    turned out to need and this solver has not been told, and check it.

    Encoding and sending are one step because they are one thing: advancing the
    fold discovers the sorts, functions and axioms the assertion mentions, and
    those have to reach this solver before the check does. -/
def Session.prove {τ σ : Type} (s : Session τ σ) (factory : @Lambda.Factory CoreLParams)
    (item : WorkItem) (satCheck validCheck : Bool) :
    IO ((Except VCError VCOutcome × LExprModel) × Session τ σ) := do
  -- Append the runs of facts this session has not walked yet. `appendEntry` takes
  -- one entry at a time, so nothing is compared: a session knows what it holds
  -- because it walked there.
  let fold := smtEncodingFold factory
  let mut core := s.core
  let mut levels := s.heldLevels
  for lvl in [s.heldLevels : item.path.size] do
    match item.path[lvl]? with
    | none => pure ()
    | some run =>
      let run := run.filter fun
        | .varDecl name _ _ => !item.skippedDefs.contains name.name
        | _ => true
      match (run.toList.forM fold.appendEntry).exec core with
      | .error e =>
        s.encodingFailure.set (some s!"{e}")
        throw (IO.userError s!"encoding failed: {e}")
      | .ok core' => core := core'
      levels := lvl + 1
  -- The axioms this goal's pruning drops are left out, exactly as on the per-obligation path.
  -- The caller has already reset the solver if it holds one of them.
  match snapshotObligation factory core item.goal.expr item.pruned with
  | .error e =>
    s.encodingFailure.set (some s!"{e}")
    throw (IO.userError s!"encoding failed: {e}")
  | .ok r =>
    -- The context to declare from is the one `snapshotObligation` returns. It encodes the goal
    -- against a fork and deliberately does not write the goal's discoveries back, so a sort,
    -- function, axiom or datatype reachable only from the goal and from no assumption on the path
    -- appears in `r.ctx` alone. Declaring from the fold's context would omit it while the goal
    -- still refers to it, and the solver would reject an unknown symbol.
    let ctx := r.ctx
    let managed := (r.varDecls.map (·.name) ++ r.varDefs.map (·.name)).foldl
      (fun acc n => acc.insert n) s.managed
    let newDatatypes := ctx.seenDatatypes.toList.filter fun n => !s.declDatatypes.contains n
    -- What this assertion needs and this solver has not been sent, by identity.
    let newSorts := ctx.sorts.toArray.toList.filter fun srt => !s.declSorts.contains srt.name
    let newUfs := ctx.ufs.toArray.toList.filter fun uf => !s.declUfs.contains uf.id
    let newIfs := ctx.ifs.toArray.toList.filter fun fn => !s.declIfs.contains fn.id
    let newAxms := ctx.axms.toArray.toList.filter fun ax => !s.declAxms.contains ax
    -- The variables a counterexample reports: the ones the goal and its path reach, as the
    -- per-obligation path chooses them.
    let vars := (collectModelVars (obligationOf item) r.varDefs r.varDecls).filterMap fun
      | (v, some ty) => some (v, Lambda.LTy.forAll [] ty)
      | (_, none) => none
    let solveTime ← IO.mkRef (0 : Nat)
    let ((sat, valid), s) ← onSolver s fun solver => do
      -- The context this assertion turned out to need, beyond what this solver has.
      declareContextAbstract solver ctx newSorts (Std.HashSet.ofList newDatatypes)
        newUfs newIfs newAxms managed
      -- The facts of this path, beyond what this solver has.
      for decl in r.varDecls.drop s.toldDecls do
        let sort ← liftM (AbstractEncoder.termTypeToSort solver decl.ty)
        let h ← liftM (solver.declareFun decl.name [] sort)
        modify fun st => { st with varHandles := st.varHandles.insert decl.name h }
      for def_ in r.varDefs.drop s.toldDefs do
        let body ← AbstractEncoder.encodeTerm solver def_.body
        let sort ← liftM (AbstractEncoder.termTypeToSort solver def_.ty)
        liftM (solver.defineFun def_.name [] sort body)
      for a in r.assumptions do
        if !s.toldAssums.contains a then
          let t ← AbstractEncoder.encodeTerm solver a
          liftM (solver.assert t)
      -- The questions, which leave the session as it was: both go through
      -- `check-sat-assuming`, so neither the goal nor its negation is ever asserted
      -- and the next goal on this branch inherits an uncontaminated context. That is
      -- also what lets both checks run against one prepared context, where the
      -- per-obligation path has to open an incremental solver to do the same.
      let g ← AbstractEncoder.encodeTerm solver r.goal
      let ng ← liftM (solver.mkNot g)
      -- A `sat` needs its counterexample taken now, while the query that produced it
      -- is still the last thing asked. It is reported as text, for the model parser the
      -- per-obligation path uses too.
      -- The program variables in scope, as terms this solver can be asked about. The lookup
      -- runs against the state as it now stands, so it sees the declarations the assumptions
      -- above just made.
      let varTerms ← (Imperative.SMT.varTermsFor (Core.SMT.typedVarToSMTFn ctx)
        vars (← get).base).mapM (AbstractEncoder.encodeTerm solver)
      let ask (lit : τ) : AbstractEncoderM τ IO (Decision × String) := do
        let t0 ← liftM (IO.monoNanosNow : IO Nat)
        let d ← liftM (solver.checkSatAssuming [lit])
        let t1 ← liftM (IO.monoNanosNow : IO Nat)
        liftM (solveTime.modify (· + (t1 - t0)) : IO Unit)
        -- A solver may refuse to report a model, after `sat` as after `unknown`; the check then
        -- stands with no counterexample, as on the per-obligation path.
        -- `(get-value ())` is not valid SMT-LIB, so a goal with no variable to report asks for
        -- nothing, as the per-obligation path does. The refusal is no encoding failure either, so
        -- what it recorded is cleared, and a later failure of the solver reads as one.
        let model ← if varTerms.isEmpty then pure "" else match d with
          | .sat | .unknown => tryCatch (liftM (solver.getModelText varTerms)) fun _ => do
              liftM (s.encodingFailure.set none : IO Unit)
              pure ""
          | _ => pure ""
        pure (d, model)
      -- A check that was not requested reports `unknown`, which is what the
      -- per-obligation path's masking expects of an outcome it did not measure.
      let sat ← if satCheck then ask g else pure (Decision.unknown, "")
      let valid ← if validCheck then ask ng else pure (Decision.unknown, "")
      pure (sat, valid)
    -- A check the solver ran out of time on is reported as the per-obligation path reports it.
    -- The counterexample is read against `ctx`, the one place that knows every datatype
    -- constructor the goal reaches, so a constructor in it comes back as one.
    let outcome ← if sat.1 == .timeout || valid.1 == .timeout then
        pure (Except.error
          (VCError.solverTimeout "solver reported a timeout on the incremental check"), [])
      else do
        let satResult ← resultOfDecision ctx vars s.enc.base sat
        let validResult ← resultOfDecision ctx vars s.enc.base valid
        pure (Except.ok
          { satisfiabilityProperty := satResult, validityProperty := validResult },
          modelOfResults ctx satResult validResult)
    return (outcome,
      { s with core := core, managed := managed,
               declSorts := newSorts.foldl (fun acc x => acc.insert x.name) s.declSorts,
               declUfs := newUfs.foldl (fun acc x => acc.insert x.id) s.declUfs,
               declIfs := newIfs.foldl (fun acc x => acc.insert x.id) s.declIfs,
               declAxms := newAxms.foldl (fun acc x => acc.insert x) s.declAxms,
               declDatatypes := newDatatypes.foldl (fun acc n => acc.insert n) s.declDatatypes,
               toldAssums := r.assumptions.foldl (fun acc a => acc.insert a) s.toldAssums,
               heldAxioms := s.heldAxioms ||| item.keptAxioms,
               toldDecls := max s.toldDecls r.varDecls.length,
               toldDefs := max s.toldDefs r.varDefs.length,
               heldLevels := levels, heldPos := item.pos,
               checks := s.checks + 1, answered := s.answered + 1,
               solveNanos := s.solveNanos + (← solveTime.get) })

/-! ## The scheduler -/


inductive Claim where
  | unclaimed
  /-- The outcome, in the shape the back end returns for any obligation. It has to be built
      while the session that produced it is alive: turning a `sat` into a model needs
      `processModel` against that session's `EncoderState`, which dies with the session, and so
      does its counterexample. -/
  | done (by_ : Nat) (outcome : Except VCError VCOutcome) (model : LExprModel)
  /-- The result of a goal session `by_` sent alone, as the per-obligation discharge built it. -/
  | sent (by_ : Nat) (result : VCResult)

instance : Inhabited Claim := ⟨.unclaimed⟩

/-- Whether this goal has no outcome yet. -/
def Claim.isUnclaimed : Claim → Bool
  | .unclaimed => true
  | _ => false

/-- Which worker proved what, and where it sat. The back end returns `VCResults`, which
    carries none of this because no consumer of a verification result needs it; the tests do,
    because "proved exactly once by one solver" and the descent order are properties of the
    schedule. -/
structure Trace where
  /-- Per goal, in tree order: where it sits, its label, and the session that proved it. -/
  perGoal : Array (Pos × String × Nat)
  /-- Per session, in plan order: its number, the checks it took, the contexts it built. -/
  perSession : Array (Nat × Nat × Nat)
  deriving Inhabited

/-! ### Workers

Sessions are workers: several exist because several run at once, and a run with
*n* sessions is a run with *n* solvers working concurrently. Each one checks the goals
`planSessions` gave it, in tree order, so what a solver is asked does not depend on
when the others finish; only when each result arrives does. `run` takes a hook that a
test can use to order those moments: before a worker takes its next goal, and when a
check has come back. Production passes `noHook`. -/

inductive Event where
  /-- About to take the next goal. -/
  | beforeClaim
  /-- A check has come back. -/
  | afterCheck
  deriving BEq, Inhabited

/-- Called with the event, the worker, and how many checks that worker has
    issued. A test uses it to order completions; production does nothing. -/
abbrev Hook := Event → Nat → Nat → IO Unit

def noHook : Hook := fun _ _ _ => pure ()

/-- Everything the workers share, held under one `Std.Mutex`: the outcomes, which a worker records
    as each check comes back, and whether the run has stopped. Every read and update goes through
    `Schedule.update`, so two workers never see the schedule half changed. -/
structure Schedule where
  /-- Per goal: no outcome yet, or done with its two verdicts. -/
  claims : Array Claim
  /-- The next session to walk that no worker has taken yet, as a position in the walked queue. -/
  next : Nat := 0
  /-- The next session to send alone that no worker has taken yet. -/
  nextAlone : Nat := 0
  /-- Per session: the checks it took and the contexts it built, once a worker has run it. -/
  perSession : Array (Option (Nat × Nat)) := #[]
  /-- Set by the first failure under `--stop-on-first-error`: from then on no worker takes
      another goal, so only the goals already being solved finish. -/
  stopped : Bool := false
  deriving Inhabited

/-- Read and change the shared schedule under its lock, returning what `f` returns. -/
private def Schedule.update {α : Type} (shared : Std.Mutex Schedule) (f : Schedule → α × Schedule) :
    IO α :=
  shared.atomically (modifyGet f)

/-- The nodes of the subtree rooted at `u`, itself included. -/
private partial def subtreeOf (l : Layout) (u : Nat) : Array Nat :=
  go #[] u
where
  go (acc : Array Nat) (v : Nat) : Array Nat :=
    (l.children.getD v #[]).foldl go (acc.push v)

/-- Record a goal's outcome. Under `--stop-on-first-error`, any
    result short of success stops the schedule, as it stops the per-obligation loop. -/
private def Schedule.finish (st : Schedule) (options : VerifyOptions) (item : WorkItem) (g : Nat)
    (by_ : Nat) (outcome : Except VCError VCOutcome) (model : LExprModel) : Schedule :=
  -- The result is built only under `--stop-on-first-error`, since this runs under the lock.
  let failed := fun (_ : Unit) =>
    ({ obligation := obligationOf item, outcome, verbose := options.verbose,
       checkLevel := options.checkLevel, checkMode := options.checkMode } : VCResult).isNotSuccess
  { st with claims := st.claims.setIfInBounds g (Claim.done by_ outcome model),
            stopped := st.stopped || (options.stopOnFirstError && failed ()) }

/-- For `workLoop`, after a proved `assert false`: the goals of session `me` in the subtree of `u`
    that the contradiction decides, given that the facts on the path to `u` contradict each other,
    each with what the solver would have answered: both checks `unsat`, for whichever of them the
    goal asks. So an `assert` reads as proved and a `cover` as unreachable, which is a failure, and
    a dead branch is still reported.

    Goals in the subtree see those facts and possibly more, so the contradiction holds for every
    one of them. Goals elsewhere do not see them and are left alone, and so are the goals of other
    sessions, which their own sessions check: deciding them here would make their verdicts depend
    on which session got there first. This reads only the layout, so it runs outside the
    schedule's lock; `decideBelow` records the outcomes under it. -/
private def decidedBelow (l : Layout) (options : VerifyOptions) (owner : Array Nat) (u : Nat)
    (me : Nat) (kept : Nat) : Array (Nat × WorkItem × VCOutcome) :=
  (subtreeOf l u).foldl (init := #[]) fun acc k =>
    (l.goalIds.getD k #[]).foldl (init := acc) fun acc g =>
      if owner.getD g me != me then acc
      else match l.tasks[g]? with
        | none => acc
        -- A goal whose pruning drops an axiom the contradiction used may not be contradictory,
        -- so it is left to a solver, as the per-obligation path would leave it.
        | some item =>
          if kept &&& item.keptAxioms != kept then acc else
          let (satCheck, validCheck) := checksFor item.goal.property item.goal.md options
          acc.push (g, item,
            { satisfiabilityProperty := if satCheck then .unsat else .unknown none,
              validityProperty := if validCheck then .unsat else .unknown none })

/-- Record, for the goals `decidedBelow` returned, the outcome of each that is still open. Recorded
    through `finish`, so a goal decided this way that counts as a failure, such as a `cover` found
    unreachable, stops a `--stop-on-first-error` run as a solved one would. -/
private def decideBelow (options : VerifyOptions) (me : Nat)
    (decided : Array (Nat × WorkItem × VCOutcome)) (st : Schedule) : Schedule :=
  decided.foldl (init := st) fun cur (g, item, outcome) =>
    -- A goal decided by a contradiction has no counterexample.
    if (cur.claims.getD g default).isUnclaimed then cur.finish options item g me (.ok outcome) []
    else cur

/-- For `workLoop`: whether proving this goal showed its context to be contradictory: the facts on
    its path and the axioms its pruning kept. `false` mentions no symbol of its own, so the only way
    it can be valid is that those cannot all hold. -/
private def provesContradiction (goal : Goal) (outcome : VCOutcome) : Bool :=
  goal.expr.isFalse && match outcome.validityProperty with
    | .unsat => true
    | _ => false

/-- One session's goals, from the `i`-th on, checked in order on one solver, for `run`. A goal on
    the path the solver holds extends it; any other makes the solver start again from the root,
    which is the only expensive move. `me` is the session, `owner` gives each goal's session, and
    `nodeOf` each goal's node. -/
private partial def workLoop {τ σ : Type} (shared : Std.Mutex Schedule) (l : Layout) (hook : Hook)
    (factory : @Lambda.Factory CoreLParams) (ctx0 : SMT.Context) (options : VerifyOptions)
    (resetPerGoal : Bool) (exactPruning : Bool)
    (spawn : IO.Ref (Option String) → IO (AbstractSolver τ σ IO))
    (owner nodeOf : Array Nat) (me : Nat) (goals : Array Nat) (i : Nat) (s : Session τ σ) :
    IO (Session τ σ) := do
  -- A solver that died between two checks fails its reset, so a session that cannot be reset is
  -- replaced by a new solver and the worker carries on.
  --
  -- A replacement that cannot be started either, such as a remote service refusing sessions
  -- for longer than `spawnPatiently` waits, leaves the worker holding the failed session: the
  -- next goal then fails on it and tries again to replace it, so a refusal costs only the goals
  -- it lasts for, as on the per-obligation path.
  --
  -- A worker that has already been refused starts each later replacement once, without waiting,
  -- so a lasting refusal costs one session start per goal, as on the per-obligation path, and
  -- no extra time.
  let replace (s : Session τ σ) : IO (Session τ σ × Option IO.Error) := do
    try pure (← s.respawn spawn ctx0 (patient := !s.dead), none)
    catch e => pure ({ s with dead := true }, some e)
  let fresh (s : Session τ σ) : IO (Session τ σ) := do
    try s.rebuild ctx0 catch _ => pure (← replace s).1
  let next := workLoop shared l hook factory ctx0 options resetPerGoal exactPruning spawn
    owner nodeOf me goals (i + 1)
  hook Event.beforeClaim s.name s.checks
  match goals[i]? with
  | none => return s
  | some g =>
    -- A goal a contradiction earlier in this session decided is skipped.
    let (stopped, open_) ← Schedule.update shared fun st =>
      ((st.stopped, (st.claims.getD g default).isUnclaimed), st)
    if stopped then return s
    if !open_ then next s else
    match l.tasks[g]? with
    | none => return s
    | some item =>
      -- A goal off the path the solver holds is checked after starting again from the root.
      let s ← if s.heldLevels > 0 && !(s.heldPos.isPrefixOf item.pos) then fresh s else pure s
      let fits := fun (g : Nat) => match l.tasks[g]? with
        | some item => s.heldAxioms &&& item.keptAxioms == s.heldAxioms
        | none => true
      let (satCheck, validCheck) := checksFor item.goal.property item.goal.md options
      -- A goal its own text settles, such as `assert true`, is decided here, as the
      -- per-obligation path decides it, without sending the solver anything.
      match evaluatorResults (obligationOf item) options.checkMode satCheck validCheck with
      | (some sat, some valid) =>
        let outcome : VCOutcome := { satisfiabilityProperty := sat, validityProperty := valid }
        -- The evaluator's verdicts carry no counterexample.
        Schedule.update shared fun st =>
          ((), st.finish options item g me (.ok outcome) [])
        next s
      | _ =>
      -- This goal's pruning drops an axiom the solver holds, which cannot be taken back. Exact
      -- pruning starts the solver again so it is told only what this goal keeps; lazy pruning
      -- keeps the context, and the goal also sees the axioms earlier goals needed.
      -- A goal that omits a definition the path holds sees a context no other goal shares, so
      -- it runs on a fresh one and leaves a fresh one behind.
      let isolated := !item.skippedDefs.isEmpty
      let s ← if isolated && s.heldLevels > 0 then fresh s
        else if fits g then pure s
        else if exactPruning then fresh s
        else pure { s with goalsWithExtraAxioms := s.goalsWithExtraAxioms + 1 }
      -- One attempt at the goal: its result and the session to go on with, or the solver's
      -- failure, the session to go on with, a new solver if one could be started, and the
      -- refusal when none could.
      let attempt (s : Session τ σ) :
          IO (Sum ((Except VCError VCOutcome × LExprModel) × Session τ σ)
            (IO.Error × Session τ σ × Option IO.Error)) := do
        s.encodingFailure.set none
        try
          pure (.inl (← s.prove factory item satCheck validCheck))
        catch e =>
          -- A goal whose terms cannot be written gets that as its result, and the rest carry
          -- on. What the solver was sent before the failure is not recorded on the session,
          -- so the session starts again from an empty solver.
          match ← s.encodingFailure.get with
          | some msg => pure (.inl ((Except.error (VCError.encoding msg), []), ← fresh s))
          | none =>
            let (s', refused) ← replace s
            pure (.inr (e, s', refused))
      -- Read as the per-obligation path reads a live solver's failure: a timeout when its message
      -- says so, such as a remote session that reached its time limit, else a crash.
      let crash (e : IO.Error) (refused : Option IO.Error) :
          Except VCError VCOutcome × LExprModel :=
        let detail := match refused with
          | some r => s!"{e}; no new solver could be started: {r}"
          | none => s!"{e}"
        (.error (match Imperative.SMT.failureOfMessage s!"{e}" with
          | .timeout _ => VCError.solverTimeout detail
          | _ => VCError.solverCrash detail), [])
      -- A solver failing after it has answered checks, such as a remote session reaching its
      -- time limit, says nothing about the goal, which is asked once more on the new solver,
      -- also when the failure comes right after the context was rebuilt. A failure on a solver
      -- that had answered nothing since it was started is the goal's own, since a new solver
      -- would be asked the same thing, and so is a second failure; either is kept to this goal,
      -- as the per-obligation path keeps it to the obligation.
      let (s, refusedBefore) ← if s.dead then replace s else pure (s, none)
      let ((outcome, model), s') ← match refusedBefore with
        | some r =>
          pure ((Except.error (VCError.solverCrash s!"no solver could be started: {r}"), []), s)
        | none => match ← attempt s with
        | .inl r => pure r
        | .inr (e, s', refused) =>
          if refused.isSome || s.answered == 0 then pure (crash e refused, s') else
          match ← attempt s' with
          | .inl r => pure r
          | .inr (e, s', refused) => pure (crash e refused, s')
      -- A contradiction decides everything below it, so nobody asks a solver for those. Only goals
      -- whose own pruning keeps every axiom the solver held may be decided this way, since those
      -- are the axioms the contradiction may have used.
      let contradiction := match outcome with
        | .ok o => provesContradiction item.goal o
        | .error _ => false
      let decided := match contradiction, nodeOf[g]? with
        | true, some u => decidedBelow l options owner u me s'.heldAxioms
        | _, _ => #[]
      Schedule.update shared fun st =>
        ((), decideBelow options me decided (st.finish options item g me outcome model))
      hook Event.afterCheck s'.name s'.checks
      -- Throwing the context away here turns this worker into one that rebuilds per goal,
      -- which is what the per-obligation path does. Everything else is unchanged, so the
      -- two runs differ only in whether the context is kept.
      let s' ← if resetPerGoal || isolated then fresh s' else pure s'
      next s'

/-- What a worker's session counted, kept once the session itself is closed and let go. -/
structure WorkerStats where
  name : Nat
  checks : Nat
  contexts : Nat
  goalsWithExtraAxioms : Nat
  solveNanos : Nat

/-- The counters of a session. -/
def WorkerStats.of {τ σ : Type} (s : Session τ σ) : WorkerStats :=
  { name := s.name, checks := s.checks, contexts := s.contexts,
    goalsWithExtraAxioms := s.goalsWithExtraAxioms, solveNanos := s.solveNanos }

/-- Walk the tree with at most `n` workers running concurrently. The sessions are planned for
    `options.minSessions`, `n` by default, and each worker takes the next session not yet taken,
    resetting its solver first. Every assertion is proved exactly once, by its session's solver.

    With `sendAlone`, a session of one goal is not walked on a solver: the worker that takes it
    sends its goal through `sendAlone`, the per-obligation discharge, since a solver opened for one
    goal shares nothing. Those sessions are taken from the same pool of `n` workers as the walked
    ones, and all start together. A solver is started only for a worker that has a session to walk,
    so a run whose sessions all hold one goal starts none. -/
def run {τ σ : Type} (factory : @Lambda.Factory CoreLParams)
    (spawn : IO.Ref (Option String) → IO (AbstractSolver τ σ IO))
    (preludeOptions : Array (String × String))
    (ctx0 : SMT.Context) (options : VerifyOptions) (tree : VTree) (n : Nat)
    (hook : Hook := noHook) (resetPerGoal : Bool := false)
    (axiomNames : List String := [])
    (prune : WorkItem → IO (List String) := fun _ => pure [])
    (sendAlone : Option (WorkItem → IO VCResult) := none) :
    IO (VCResults × Statistics × Trace) := do
  let exactPruning := options.exactPruning
  let l0 := layoutOf tree
  let bit : Std.HashMap String Nat :=
    (axiomNames.zip (List.range axiomNames.length)).foldl (fun m (n, i) => m.insert n i) {}
  -- Each goal's pruning, decided once from the goal and its path alone.
  let tasks ← l0.tasks.mapM fun t => do
    let pruned ← prune t
    let dropped : Std.HashSet String := Std.HashSet.ofList pruned
    let keptMask := t.path.foldl (init := 0) fun acc run =>
      run.foldl (init := acc) fun acc entry => match entry with
        | .assumption label _ =>
          match bit.get? label with
          | some i => if dropped.contains label then acc else acc ||| (1 <<< i)
          | none => acc
        | _ => acc
    -- The per-obligation discharge drops a goal's unused CSE definitions only when one of them
    -- holds a string literal SMT-LIB cannot spell; doing the same here keeps such a literal from
    -- failing every goal below the node it was hoisted to.
    let ob := obligationOf t
    let skippedDefs : Std.HashSet String :=
      if !hasUnsupportedStringCSEDefinition ob then {} else
        let defsOf (o : Imperative.ProofObligation Expression) : List String :=
          o.assumptions.flatMap fun pc => pc.filterMap fun
            | .varDecl name _ (.det _) =>
              if CSE.isCSEGeneratedName name.name then some name.name else none
            | _ => none
        let keptDefs := Std.HashSet.ofList (defsOf (pruneUnusedCSEDefinitions ob))
        Std.HashSet.ofList ((defsOf ob).filter (!keptDefs.contains ·))
    pure { t with pruned, keptAxioms := keptMask, skippedDefs }
  let l := { l0 with tasks }
  let sessions := planSessions l (options.minSessions.getD n) options.splitByNode
  let alone := fun (j : Nat) => sendAlone.isSome && (sessions.getD j #[]).size == 1
  let queue := (List.range sessions.size).toArray.filter (!alone ·)
  let aloneQueue := (List.range sessions.size).toArray.filter alone
  let workers := min (max 1 n) sessions.size
  -- Only the workers with a session to walk need a solver.
  let solverWorkers := min workers queue.size
  let owner := sessions.size.fold (init := Array.replicate l.tasks.size 0) fun j _ acc =>
    (sessions.getD j #[]).foldl (fun a g => a.setIfInBounds g j) acc
  let nodeOf := l.goalIds.size.fold (init := Array.replicate l.tasks.size 0) fun u _ acc =>
    (l.goalIds.getD u #[]).foldl (fun a g => a.setIfInBounds g u) acc
  let shared ← Std.Mutex.new { claims := Array.replicate l.tasks.size Claim.unclaimed,
                                perSession := Array.replicate sessions.size none : Schedule }
  -- Every solver process the run starts, including the ones a worker starts to replace a
  -- failed solver, is recorded as it is spawned. Closing that record at the end, whatever
  -- happened to the workers, is what guarantees no process outlives the run.
  -- A solver leaves the record once it is closed, so one a worker replaced is not held until
  -- the end.
  let spawned ← Std.Mutex.new (({} : Std.HashMap Nat (AbstractSolver τ σ IO)), (0 : Nat))
  let closeAll : IO Unit := do
    for (_, sv) in (← spawned.atomically get).1 do try sv.close catch _ => pure ()
  let spawn := fun (failed : IO.Ref (Option String)) => do
    let sv ← spawn failed
    let id ← spawned.atomically (modifyGet fun (m, n) => (n, (m.insert n sv, n + 1)))
    pure { sv with close := do
      try sv.close finally spawned.atomically (modify fun (m, n) => (m.erase id, n)) }
  -- The workers' solvers are started together, so all of them wait out a refusal at the same
  -- time. A worker whose solver cannot be started is left out, with a warning, and the
  -- others take its sessions; with none started, the run fails, so its caller can fall back.
  let starts ← (List.range solverWorkers).mapM fun j => IO.asTask (prio := .dedicated) do
    let failed ← IO.mkRef none
    Session.open j (← spawnPatiently spawn failed) failed preludeOptions ctx0
  let mut opened : Array (Session τ σ) := #[]
  let mut startError : Option IO.Error := none
  for t in starts do
    match ← IO.wait t with
    | .ok s => opened := opened.push s
    | .error e => if startError.isNone then startError := some e
  if let some e := startError then
    if opened.isEmpty then
      closeAll
      throw (IO.userError s!"{noSolverStarted}{e}")
    IO.eprintln s!"incremental: {solverWorkers - opened.size} of {solverWorkers} solvers could not \
      be started, going on with {opened.size}: {e}"
  -- A worker takes sessions in plan order until none is left, and resets its solver between two,
  -- so a session is checked from an empty solver whichever worker takes it, and a run planned for
  -- many sessions can be replayed with fewer solvers. A solver that cannot be reset is replaced.
  -- A session sent alone: its goal goes through `sendAlone`, and a failure to send it is that
  -- goal's own, reported as a crash.
  let sendOne (j : Nat) : IO Unit := do
    match (sessions.getD j #[])[0]?, sendAlone with
    | some g, some send =>
      match l.tasks[g]? with
      | none => pure ()
      | some item =>
        let crashed (e : IO.Error) : VCResult :=
          { obligation := obligationOf item, outcome := .error (VCError.solverCrash s!"{e}"),
            verbose := options.verbose, checkLevel := options.checkLevel,
            checkMode := options.checkMode }
        let r ← try send item catch e => pure (crashed e)
        Schedule.update shared fun st =>
          ((), { st with claims := st.claims.setIfInBounds g (Claim.sent j r),
                         stopped := st.stopped || (options.stopOnFirstError && r.isNotSuccess) })
    | _, _ => pure ()
  -- The next session sent alone nobody has taken yet, if the run goes on.
  let takeAlone : IO (Option Nat) := Schedule.update shared fun st =>
    if st.stopped || st.nextAlone ≥ aloneQueue.size then (none, st)
    else (aloneQueue[st.nextAlone]?, { st with nextAlone := st.nextAlone + 1 })
  -- A worker without a solver only sends sessions alone.
  let mut aloneHandles : Array (Task (Except IO.Error Unit)) := #[]
  if !aloneQueue.isEmpty then
    for _ in [opened.size : workers] do
      aloneHandles := aloneHandles.push (← IO.asTask (prio := .dedicated) do
        repeat
          match ← takeAlone with
          | none => break
          | some j => sendOne j)
  -- A worker walks sessions until none is left to walk, and returns its session.
  let walkAll (s : Session τ σ) : IO (Session τ σ) := do
    let mut s := s
    let mut first := true
    repeat
      let j ← Schedule.update shared fun st =>
        if st.stopped || st.next ≥ queue.size then (none, st)
        else (queue[st.next]?, { st with next := st.next + 1 })
      match j with
      | none => break
      | some j =>
        let (checks, contexts) := if first then (0, 0) else (s.checks, s.contexts)
        -- A solver that can neither be reset nor replaced is marked dead, so the session's first
        -- goal tries again to replace it and only the goals checked while the refusal lasts
        -- report it, as within a session.
        if !first then
          s ← try s.rebuild ctx0 catch _ =>
            try s.respawn spawn ctx0 (patient := !s.dead)
            catch _ => pure { s with dead := true }
        first := false
        s ← workLoop shared l hook factory ctx0 options resetPerGoal exactPruning spawn
          owner nodeOf j (sessions.getD j #[]) 0 s
        let done := (s.checks - checks, s.contexts - contexts)
        Schedule.update shared fun st =>
          ((), { st with perSession := st.perSession.setIfInBounds j (some done) })
    return s
  -- With nothing left to walk, a worker closes its solver and keeps only its counters, so nothing
  -- refers to the session any more and a remote one is released, and then sends sessions alone:
  -- a worker never holds a solver of its own while the discharge holds another for a goal it
  -- sends.
  let mut handles : Array (Task (Except IO.Error WorkerStats)) := #[]
  for s in opened do
    handles := handles.push (← IO.asTask (prio := .dedicated) do
      let stats ← (do
        let s ← walkAll s
        try s.close catch _ => pure ()
        pure (WorkerStats.of s))
      repeat
        match ← takeAlone with
        | none => break
        | some j => sendOne j
      pure stats)
  let mut finals : Array WorkerStats := #[]
  -- A worker's own failure is reported before a refused start, which is kept for goals no
  -- started worker reached.
  let mut firstError : Option IO.Error := none
  for h in handles do
    match h.get with
    | .ok s => finals := finals.push s
    | .error e => if firstError.isNone then firstError := some e
  for h in aloneHandles do
    match h.get with
    | .ok () => pure ()
    | .error e => if firstError.isNone then firstError := some e
  firstError := firstError <|> startError
  -- Each close is best-effort: a solver a worker already replaced is closed, and closing it
  -- again must not stop the rest from being closed.
  closeAll
  -- A worker that could not go on leaves the goal it held, and any nobody reached, without a
  -- verdict; they report its failure, and every goal another worker proved keeps its result.
  do
    let st ← Schedule.update shared fun st => (st, st)
    -- A stopped run reports the goals it reached, as the per-obligation loop does when it stops.
    let tasks := if st.stopped then
      tasks.filter fun t => !(st.claims.getD t.id default).isUnclaimed else tasks
    let results : VCResults := tasks.map fun t =>
      match st.claims.getD t.id default with
      | .sent _ r => r
      | .done _ outcome model =>
        { obligation := obligationOf t, outcome,
          verbose := options.verbose, checkLevel := options.checkLevel,
          checkMode := options.checkMode, lexprModel := model }
      | .unclaimed =>
        -- No verdict was obtained, which `unknown` says.
        let outcome := match firstError with
          | some e => .error (VCError.solverCrash s!"{e}")
          | none =>
            .ok { satisfiabilityProperty := .unknown none, validityProperty := .unknown none }
        { obligation := obligationOf t, outcome,
          verbose := options.verbose, checkLevel := options.checkLevel,
          checkMode := options.checkMode }
    let trace : Trace :=
      { perGoal := tasks.map fun t =>
          (t.pos, t.goal.label, match st.claims.getD t.id default with
            | .done by_ _ _ | .sent by_ _ => by_
            -- Only a run whose workers failed reports a goal without an outcome.
            | .unclaimed => 0),
        -- A session no worker took, in a stopped run, is left out.
        perSession := (List.range sessions.size).toArray.filterMap fun j =>
          (st.perSession.getD j none).map fun (checks, contexts) => (j, checks, contexts) }
    -- Per-worker counters go where the pipeline already carries measurements.
    let stats := finals.foldl (init := ({} : Statistics)) fun acc s =>
      (((acc.increment s!"incremental.worker{s.name}.checks" s.checks).increment
        s!"incremental.worker{s.name}.contexts" s.contexts).increment
        "incremental.goalsWithExtraAxioms" s.goalsWithExtraAxioms).increment
        "incremental.solveMs" (s.solveNanos / 1000000)
    let sent := (st.claims.filter fun | .sent .. => true | _ => false).size
    return (results, stats.increment "incremental.sentAlone" sent, trace)

/-! ## Entry point

A verifier that walks the tree, checking the goals below a node on one solver.
It takes what `verifySingleEnv` takes: a program whose procedure bodies are in the
form `ObligationExtraction` accepts. Nothing upstream has to run, which is what
lets this be tested without `symbolicEval`. -/

/-- Each goal's pruning, which `verifyProgram` and `verifyProgramWith` hand to `run`: the
    per-obligation path's own decision for it, so a goal is asked exactly
    the question that path asks. The relevance query runs against the program as it was before
    the pipeline, as it does there. -/
private def pruneFor (options : VerifyOptions) (program : Program) (axiomProgram : Option Program) :
    WorkItem → IO (List String) :=
  if options.removeIrrelevantAxioms == .Off then fun _ => pure [] else
  let axProg := axiomProgram.getD program
  let axiomNames := axiomNamesOf axProg
  let cache := IrrelevantAxioms.Cache.build axProg
  fun item => do
    let (satCheck, validCheck) := checksFor item.goal.property item.goal.md options
    let (_, _, _, labels) ← EIO.toIO (fun m => IO.userError (toString (m.format none)))
      (preprocessObligation (obligationOf item) program options satCheck validCheck
        (some cache) axiomNames (axiomProgram := some axProg))
    pure labels

/-- Where the solvers a run walks the tree with come from. Any `AbstractSolver` will do, so a
    remote service can stand in for the local processes: each call to `spawn` is one solver,
    kept for the whole walk and reset when a worker returns to the root. `prelude` is the
    `set-option`s each solver starts from, and is sent again after every reset.

    Such a solver reports every failure as an `IO.Error`, so a term it cannot write is not told
    apart from a failing session: the goal is asked once more on a new solver and then reports
    a solver crash, where a local process reports an encoding error. -/
structure SessionFactory where
  τ : Type
  σ : Type
  spawn : VerifyOptions → IO (AbstractSolver τ σ IO)
  prelude : Array (String × String) := #[]

/-- Verify a program by walking its obligation tree with `sessions` solvers, opened by
    `session`, or local solver processes when it is `none`. -/
def verifyProgramWith (session : SessionFactory) (program : Program) (sessions : Nat := 1)
    (options : VerifyOptions := VerifyOptions.quiet)
    (factory : @Lambda.Factory CoreLParams := Factory)
    (axiomProgram : Option Program := none)
    (sendAlone : Option (WorkItem → IO VCResult) := none) :
    IO (Except Format (VCResults × Statistics × Trace)) := do
  match buildEnv options program factory (registerCustomFunctions := true) with
  | .error e => return .error f!"{e.message}"
  | .ok (E, _) =>
    match readProgram program with
    | .error e => return .error f!"{e}"
    | .ok tree =>
      let smtCtx := { SMT.Context.default with
        datatypes := SMT.Datatypes.ofFactory E.datatypes,
        useArrayTheory := options.useArrayTheory,
        recFnsAsDefineFunRec := options.recursiveFnsAsDefineFunRec }
      let r ← run E.factory (fun _ => session.spawn options) session.prelude smtCtx options tree
        sessions noHook false (axiomNamesOf (axiomProgram.getD program))
        (pruneFor options program axiomProgram) sendAlone
      return .ok r

/-- Verify a program by walking its obligation tree with `sessions` solvers.

    `wrapSolver` is applied to every solver this opens. It is the identity in production; a test
    passes a wrapper that observes what reaches the solver, such as how many checks it is asked,
    which the engine's own counters cannot vouch for.

    With `removeIrrelevantAxioms` on, each goal keeps the axioms the per-obligation path keeps for
    it. Pruning is lazy by default: a solver is sent the kept axioms it does not hold yet and never
    takes one back, so a goal after the first may also see axioms earlier goals needed.
    `options.exactPruning` resets the solver instead when a goal drops an axiom it holds, so every
    goal is asked the per-obligation question. -/
def verifyProgram (program : Program) (sessions : Nat := 1)
    (options : VerifyOptions := VerifyOptions.quiet)
    (factory : @Lambda.Factory CoreLParams := Factory)
    (hook : Hook := noHook) (resetPerGoal : Bool := false)
    (wrapSolver : AbstractSolver Term TermType IO → AbstractSolver Term TermType IO := id)
    (axiomProgram : Option Program := none)
    (sendAlone : Option (WorkItem → IO VCResult) := none) :
    IO (Except Format (VCResults × Statistics × Trace)) := do
  match buildEnv options program factory (registerCustomFunctions := true) with
  | .error e => return .error f!"{e.message}"
  | .ok (E, _) =>
    match readProgram program with
    | .error e => return .error f!"{e}"
    | .ok tree =>
      let smtCtx := { SMT.Context.default with
        datatypes := SMT.Datatypes.ofFactory E.datatypes,
        useArrayTheory := options.useArrayTheory,
        recFnsAsDefineFunRec := options.recursiveFnsAsDefineFunRec }
      -- Started as the one-shot incremental discharge starts its solver, so a goal gets the same
      -- time limit, and an `unknown` at it the same reading, whichever of the two sends it.
      let launch := SMT.incrementalLaunch options
      let spawn (failed : IO.Ref (Option String)) : IO (AbstractSolver Term TermType IO) := do
        let st ← IncrementalSolver.spawn options.solver launch.flags
          (timeLimitMs := launch.timeLimitMs)
        return wrapSolver (raisingIn (IncrementalSolver.mkIncrementalSolver st) failed)
      let r ← run E.factory spawn launch.prelude
        smtCtx options tree sessions hook resetPerGoal
        (axiomNamesOf (axiomProgram.getD program)) (pruneFor options program axiomProgram)
        sendAlone
      return .ok r

/-- The validity verdict, which is the one every `assert` gets in deductive mode. A goal
    checked only for satisfiability reports `unknown` here and its verdict is the outcome's
    other field. -/
def verdictOf (r : VCResult) : String :=
  match r.outcome with
  | .error (.solverTimeout _) => "timeout"
  | .error _ => "error"
  | .ok o => match o.validityProperty with
    | .unsat => "proved"
    | .sat _ => "REFUTED"
    | .unknown _ => "unknown"
    | .err _ => "error"

/-- Whether every goal's validity check came back `unsat`, as `verdictOf` reads it: every
    `assert` proved. A `cover`, checked for satisfiability alone, never counts as proved here. -/
def allProved (results : VCResults) : Bool :=
  results.all fun r => verdictOf r == "proved"

/-- One line per assertion, then one per worker. Names the worker, so it is only stable when
    the interleaving is scripted or there is one worker. -/
def Trace.format (t : Trace) (results : VCResults) : String :=
  let goals := (t.perGoal.zip results).toList.map fun (g, r) =>
    s!"{g.2.1}: session {g.2.2} {verdictOf r}"
  let sess := t.perSession.toList.map fun p =>
    s!"session {p.1}: {p.2.1} checks, {p.2.2} contexts"
  String.intercalate "\n" (goals ++ sess)

/-- What holds of a run whatever order the solvers finished in: how many assertions there
    were, how many checks it took, and whether everything was proved. Checks equal to
    assertions is the exactly-once property. Contexts are deliberately absent: how many get
    built depends on how far workers wander, which depends on the timing. -/
def Trace.invariants (t : Trace) (results : VCResults) : String :=
  let checks := t.perSession.foldl (fun a p => a + p.2.1) 0
  s!"{results.size} assertions, {checks} checks, all proved: {allProved results}"

/-- What a run looks like without naming workers: per position, how many assertions sat there
    and how many distinct workers proved them; then the workloads, sorted. Stable under any
    interleaving, so a parallel run can be asserted on without scripting it. -/
def Trace.shape (t : Trace) (results : VCResults) : String :=
  let goals := t.perGoal.zip results
  let positions := goals.foldl (init := (#[] : Array Pos)) fun acc (g, _) =>
    if acc.any (fun p => p == g.1) then acc else acc.push g.1
  let arms := positions.toList.map fun p =>
    let here := goals.filter fun (g, _) => g.1 == p
    let provers := here.foldl (init := (#[] : Array Nat)) fun acc (g, _) =>
      if acc.any (fun q => q == g.2.2) then acc else acc.push g.2.2
    let proved := here.all fun (_, r) => verdictOf r == "proved"
    s!"node {p.toList}: {here.size} assertions, {provers.size} solver(s)" ++
      (if proved then "" else ", SOME FAILED")
  let loads := (t.perSession.toList.map fun p => (p.2.1, p.2.2)).mergeSort
    (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2))
  let loadLine := "workloads: " ++ String.intercalate ", "
    (loads.map fun l => s!"{l.1} checks/{l.2} contexts")
  String.intercalate "\n" (arms ++ [loadLine])

/-- The tree verifier as the pipeline's `vcDischarge` back end. Takes what any `CoreSMTSolver`
    takes, the complete factory and the program after all transformations, and returns what any
    of them returns. The schedule diagnostics a run also produces are dropped here: they say
    which worker did what, which no consumer of a verification result asks.

    Every goal is planned into a session. A session of one goal shares a context with nothing, so
    it is sent the way the per-obligation path sends it, one request for that goal alone, through
    `mkDischarge` and with that path's pruning, and its verdict is that path's by construction. The
    other sessions are walked on the solvers `session` opens, or on local solver processes. Both
    kinds are taken from one pool of `sessions` workers and start together, and the results come
    back in the program's order.

    The factory arrives complete, so it goes to `buildEnv` untouched: adding to it would re-add
    Core's built-ins and fail on duplicates.

    With `sendAlone := false`, the sessions of one goal are walked too, which is how the tests
    compare the walk itself with the per-obligation path on programs whose goals would otherwise
    all be sent alone. -/
def coreSMTSolver (sessions : Nat := 1) (options : VerifyOptions := VerifyOptions.quiet)
    (axiomProgram : Option Program := none)
    (session : Option SessionFactory := none)
    (mkDischarge : MkDischargeFn := mkDischargeFn) (sendAlone : Bool := true) :
    CoreSMTSolver := fun factory oblProgram => do
  let toMsg := fun (e : IO.Error) => Strata.Pipeline.Message.fromFormat f!"{e}"
  let ofMsg := fun (m : Strata.Pipeline.Message) => IO.userError (toString (m.format none))
  let axProg := axiomProgram.getD oblProgram
  let axiomNames := axiomNamesOf axProg
  let axiomCache := if options.removeIrrelevantAxioms == .Off then none
    else some (IrrelevantAxioms.Cache.build axProg)
  let pctx ← (Strata.Pipeline.PipelineContext.create (outputMode := .quiet) : BaseIO _)
  let counter ← IO.toEIO toMsg (IO.mkRef 0)
  IO.toEIO toMsg <| IO.FS.withTempDir fun tempDir => do
    -- The per-obligation path, for a run that can start no solver at all.
    let perObligation : IO (VCResults × Statistics) :=
      EIO.toIO ofMsg ((mkDefaultCoreSMTSolver options counter tempDir axiomCache axiomNames
        (axiomProgram := axProg) (mkDischarge := mkDischarge) (pctx := pctx) : CoreSMTSolver)
        factory oblProgram)
    -- A goal sent alone is discharged against the environment of the whole program, as the
    -- per-obligation path discharges it, and with that path's dropping of unused CSE definitions,
    -- which it applies to every obligation once one needs it.
    let anyUnsupportedCSE := match ObligationExtraction.extractObligations oblProgram with
      | .ok obs => obs.any hasUnsupportedStringCSEDefinition
      | .error _ => false
    -- Built on the first goal sent alone, and once, however many workers send at once.
    let env : Thunk (Except Strata.Pipeline.Message Env) := Thunk.mk fun _ =>
      (Core.buildEnv options oblProgram factory (registerCustomFunctions := true)).map (·.1)
    let sendOne (item : WorkItem) : IO VCResult := do
      let E ← match env.get with
        | .ok E => pure E
        | .error m => throw (ofMsg m)
      let ob := obligationOf item
      let ob := if anyUnsupportedCSE then pruneUnusedCSEDefinitions ob else ob
      -- The caller's worker count is kept: several workers may send goals at once, and a back end
      -- that shares one connection across a sequential run relies on `parallelWorkers` to tell it
      -- when obligations may be sent concurrently. Each goal gets a pipeline context of its own,
      -- since a context's phase stack is not meant to be shared by concurrent workers, and nothing
      -- reads these contexts back.
      let goalCtx ← (Strata.Pipeline.PipelineContext.create (outputMode := .quiet) : BaseIO _)
      let (rs, _) ← EIO.toIO ofMsg (dischargeObligations E #[ob]
        { options with stopOnFirstError := false } counter tempDir
        axiomCache axiomNames (axiomProgram := axProg) (mkDischarge := mkDischarge) (pctx := goalCtx))
      match rs[0]? with
      | some r => pure r
      | none => throw (IO.userError s!"no result for {item.goal.label}")
    let alone := if sendAlone then some sendOne else none
    let walked ← try
        pure (Sum.inl (← match session with
          | some f =>
            verifyProgramWith f oblProgram sessions options factory
              (axiomProgram := axiomProgram) (sendAlone := alone)
          | none =>
            verifyProgram oblProgram sessions options factory
              (axiomProgram := axiomProgram) (sendAlone := alone)))
      catch e => pure (Sum.inr e)
    match walked with
    | .inr e =>
      -- Only a run that started no solver falls back; any other failure is the run's own.
      let msg := toString e
      unless msg.startsWith noSolverStarted do throw e
      IO.eprintln s!"{msg}; every goal is sent alone"
      perObligation
    | .inl (.error e) => throw (IO.userError (toString e))
    | .inl (.ok (results, stats, _)) => pure (results, stats)

end

end Core.IncrementalSolve

/-! ## Choosing the verification back end

`Core.verify` is the entry point every front end verifies a Core program through: Core
programs read by `strata verify`, and the programs the Laurel and Python front ends
translate to Core. It decides which back end discharges the obligations, the obligation-tree
walk above or one solver per obligation, and runs the pipeline of
`verifyPipeline` with it. Making that choice here, in the one function they all call, is
what gives every front end the tree walk under `--incremental`.
-/

namespace Core

public section

/--
Run the Strata Core verification pipeline on `program`, keeping SMT files in `tempDir`
when the per-obligation path writes them. See `verifyPipeline` for the pipeline itself.

The back end is chosen as follows.
- A `solver` passed in is used as it is.
- Otherwise, under `--incremental`, the obligation tree is walked, sharing one solver
  session down a branch. The tree is walked on the sessions `mkSession` opens, or on local
  solver processes, but never on local processes for a caller with its own `mkDischarge`
  and no sessions: that caller decides where queries go. Goals alone in their procedure
  go through `mkDischarge` either way.
- Otherwise each obligation is sent on its own through `mkDischarge`.

The per-obligation path is kept, under `--incremental` too, when SMT files are to be kept
(`vcDirectory`, `alwaysGenerateSMT`) or a subset of the obligations is asked for by label
(`obligationsToVerify`): that path is the only one that writes and filters them. A
`vcDirectory` also turns `--incremental` off for that path, which writes SMT files only
when it is not incremental.
-/
def verify (program : Program)
    (tempDir : System.FilePath)
    (options : VerifyOptions := VerifyOptions.default)
    (moreFns : @Lambda.Factory CoreLParams := Lambda.Factory.default)
    (externalPhases : List AbstractedPhase := [])
    (entryFacts : ProgramFactSet := ProgramFactSet.empty)
    (pipeline : Option (ValidatedPipeline entryFacts) := none)
    (entryFactsHold : entryFacts.holds program :=
      by exact _root_.Core.ProgramFactSet.empty_holds _)
    (solver : Option CoreSMTSolver := none)
    (mkDischarge : Option MkDischargeFn := none)
    (pipelineCtx : Option Strata.Pipeline.PipelineContext := none)
    (mkSession : Option IncrementalSolve.SessionFactory := none)
    : EIO Strata.Pipeline.Message VCResults := do
  let options := if options.vcDirectory.isSome then { options with incremental := false }
    else options
  let walkable := (mkSession.isSome || mkDischarge.isNone) && options.obligationsToVerify.isNone
  let mkDischarge := mkDischarge.getD mkDischargeFn
  let solver := match solver with
    | some s => some s
    | none =>
      if options.incremental && !options.alwaysGenerateSMT && walkable then
        some (IncrementalSolve.coreSMTSolver options.parallelWorkers options
          (axiomProgram := some program) (session := mkSession) (mkDischarge := mkDischarge))
      else none
  verifyPipeline program tempDir options moreFns externalPhases
    (entryFacts := entryFacts) (pipeline := pipeline) (entryFactsHold := entryFactsHold)
    (solver := solver) (mkDischarge := mkDischarge) (pipelineCtx := pipelineCtx)

end -- public section

end Core
