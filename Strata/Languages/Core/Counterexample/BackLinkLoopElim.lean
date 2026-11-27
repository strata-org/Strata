/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.BackLinkChainReplay
public import Strata.Transform.LoopElim
import Strata.DL.Imperative.Counterexample.Tactics

/-! # `loopElim` back-link support: configuration mapping and slicing

Support for the `(a) → (a)` back-link of the loop-elimination phase
`loopElimPipelinePhase` ([LoopElim.lean](Strata/Transform/LoopElim.lean)): mapping a
configuration of the pass's output to the source, and slicing a source replay at loop
entries and exits.

## What the pass abstracts

`removeLoop` rewrites a bare loop `loop (G) { B }` (with `M` the loop-carried variables,
`Block.modifiedVars B` minus `Block.definedVars B false`, in that order) into

```
if (G) {
  block $__loopElim_arbitrary_iter_facts_n {
    block $__loopElim_havoc_n { havoc M };   -- an arbitrary mid-loop state
    assume $__loopElimAssume_guard_n (G);    -- (`true` for a nondet guard)
    B                                        -- one arbitrary iteration
  };
  block $__loopElim_havoc_n { havoc M };     -- an arbitrary exit state
  assume $__loopElimAssume_not_guard_n (¬G)  -- (`true` for a nondet guard)
}
```

iterating to a fixed point, so nested loops are eliminated too.  The downstream run
picks the mid-loop and the exit states freely; upstream, the loop's history before the
mid-loop state and after the one iteration are open reachability questions.  So each
loop on the failing path cuts the lifted counterexample twice: at its entry (cut 1) and
at its exit (cut 2).

## Oracle alignment

The downstream `if (G)` draws a branch choice exactly where the upstream loop's first
guard decision does (only for a nondet guard); each havoc block draws `|M|` values in
`M` order; the assumes and blocks draw nothing; `B` is copied verbatim.  So a replay of
the source consumes the downstream oracle identically, provided it pops `|M|` values at
each of the two cuts.

## The pieces in this file

* `loopOriginsProgram` — for every eliminated loop, the label of its arbitrary-iteration
  block paired with the source loop, found by walking the phase's input and output
  bodies in parallel (the pass replaces each loop in place by one `if`).
* `unloopElimConfig` — maps a configuration of the pass's output to the source.
* `loopExpansionFreeStmts` / `LoopElimImageStmts` — the statement lists on which
  `unloopElimConfig` is the identity, and the downstream images of a source unit.
* `loopElimCutHandler` / `loopElimSlice` — the loop cut rule of the shared slicing
  replay (`sliceRun`, `BackLinkChainReplay.lean`).
-/

namespace Core

open _root_.Lambda Imperative

public section

/-- Label prefix of the arbitrary-iteration block of an eliminated loop. -/
def loopElimArbitraryIterPrefix : String := s!"{loopElimBlockPrefix}arbitrary_iter_facts_"

/-- The source loop of each eliminated loop, keyed by the label of its
    arbitrary-iteration block. -/
abbrev LoopOrigins := List (String × Statement)

/-- The number of statements of an arbitrary-iteration block before the loop body: the havoc
    block and the guard assumptions the pass emits (`LoopElim.enterAssume`). -/
def loopElimBodyOffset (guard : ExprOrNondet Expression) : Nat :=
  1 + (LoopElim.enterAssume (C := Command) "" guard {}).length

mutual

/-- Walk a source statement and the statement the pass put in its place, recording each
    eliminated loop (a source `loop` whose image is an `if` headed by an
    arbitrary-iteration block) and recursing into its body. -/
def loopOriginsStmt : Statement → Statement → LoopOrigins
  | .loop guard measure invariants body md, .ite _ (.block label inner _ :: _) [] _ =>
    if label.startsWith loopElimArbitraryIterPrefix then
      (label, .loop guard measure invariants body md) ::
        loopOriginsStmts body (inner.drop (loopElimBodyOffset guard))
    else []
  | .block _ body _, .block _ body' _ => loopOriginsStmts body body'
  | .ite _ thenB elseB _, .ite _ thenB' elseB' _ =>
    loopOriginsStmts thenB thenB' ++ loopOriginsStmts elseB elseB'
  | _, _ => []

/-- Walk two statement lists in parallel (`loopOriginsStmt` position by position). -/
def loopOriginsStmts : List Statement → List Statement → LoopOrigins
  | s :: rest, s' :: rest' => loopOriginsStmt s s' ++ loopOriginsStmts rest rest'
  | _, _ => []

end

/-- The loop origins of a whole program: every structured procedure of the phase's
    `input`, walked in parallel with the same-named procedure of its `output`. -/
def loopOriginsProgram (input output : Program) : LoopOrigins :=
  input.decls.flatMap fun declaration =>
    match declaration with
    | .proc procedure _ =>
      match procedure.body with
      | .structured body _ =>
        let body'? := output.decls.findSome? fun declaration' =>
          match declaration' with
          | .proc procedure' _ =>
            if procedure'.header.name.1 == procedure.header.name.1 then
              match procedure'.body with
              | .structured body' _ => some body'
              | .cfg _ _ | .abstract => none
            else none
          | _ => none
        match body'? with
        | some body' => loopOriginsStmts body body'
        | none => []
      | .cfg _ _ | .abstract => []
    | _ => []

/-! ## Mapping a downstream configuration upstream (`unloopElimConfig`) -/

/-- A statement the pass introduced inside an expansion: a block it labelled
    (`$__loopElim_…`) or an assumption it labelled (`$__loopElimAssume_…`). -/
def isLoopElimInternal (s : Statement) : Bool :=
  match s with
  | .block label _ _ => label.startsWith loopElimBlockPrefix
  | .cmd (.cmd (.assume label _ _)) => label.startsWith loopElimAssumePrefix
  | _ => false

/-- Whether the statement list starts with a statement the pass introduced. -/
def headIsLoopElimInternal (ss : List Statement) : Bool :=
  match ss with
  | s :: _ => isLoopElimInternal s
  | [] => false

mutual

/-- A statement with every expansion (an `if` headed by a recorded arbitrary-iteration
    block) replaced by its source loop. -/
def unloopStmt (origins : LoopOrigins) : Statement → Statement
  | .ite guard (.block label inner md' :: rest) [] md =>
    match origins.lookup label with
    | some loop => loop
    | none => .ite guard (unloopStmts origins (.block label inner md' :: rest)) [] md
  | .ite guard thenB elseB md =>
    .ite guard (unloopStmts origins thenB) (unloopStmts origins elseB) md
  | .block label body md => .block label (unloopStmts origins body) md
  | .loop guard measure invariants body md =>
    .loop guard measure invariants (unloopStmts origins body) md
  | .cmd c => .cmd c
  | .exit label md => .exit label md
  | .typeDecl tc md => .typeDecl tc md

/-- `unloopStmt` on every statement of a list. -/
def unloopStmts (origins : LoopOrigins) : List Statement → List Statement
  | [] => []
  | s :: rest => unloopStmt origins s :: unloopStmts origins rest

end

/-- **Map a downstream configuration upstream.**

    * Frames outside expansions map to themselves, with their statements un-eliminated;
      the stores are unchanged (the pass introduces no variables), and every scope frame
      becomes an embedded frame (`defined = none`).
    * A position inside the one iteration of an expansion (inside its
      arbitrary-iteration block, past the havoc and the guard assumption) maps to the
      same position of an upstream iteration: the iteration's anonymous block,
      continued by the loop itself.
    * A position at a statement the pass introduced (a havoc block, a guard assumption,
      the start of the expansion's `then` branch) has no upstream counterpart: `none`. -/
def unloopElimConfig (origins : LoopOrigins) :
    IConfig Expression Command → Option (IConfig Expression Command)
  | .stmt s env =>
    if isLoopElimInternal s then none else some (.stmt (unloopStmt origins s) env)
  | .stmts ss env =>
    if headIsLoopElimInternal ss then none else some (.stmts (unloopStmts origins ss) env)
  | .terminal env => some (.terminal env)
  | .exiting label env => some (.exiting label env)
  | .seq (.terminal env) rest =>
    if headIsLoopElimInternal rest then none
    else some (.seq (.terminal env) (unloopStmts origins rest))
  | .seq inner rest =>
    (unloopElimConfig origins inner).map fun inner' => .seq inner' (unloopStmts origins rest)
  | .seqs inner k => (unloopElimConfig origins inner).map fun inner' => .seqs inner' k
  | .block none fr (.seq (.block (some label) fr' iter) thenRest) =>
    match origins.lookup label with
    | some loop =>
      (unloopElimConfig origins iter).map fun iter' =>
        .seq (.block none { fr' with defined := none } iter') [loop]
    | none =>
      (unloopElimConfig origins (.seq (.block (some label) fr' iter) thenRest)).map
        fun inner' => .block none { fr with defined := none } inner'
  | .block label fr inner =>
    match label with
    | some l =>
      if l.startsWith loopElimBlockPrefix then none
      else (unloopElimConfig origins inner).map fun inner' =>
        .block label { fr with defined := none } inner'
    | none => (unloopElimConfig origins inner).map fun inner' =>
        .block label { fr with defined := none } inner'

/-! ### Expansion-free statements -/

mutual

/-- No expansion occurs in `s` (no `if` headed by a recorded arbitrary-iteration block
    at any depth). -/
def loopExpansionFreeStmt (origins : LoopOrigins) : Statement → Prop
  | .ite _ thenB elseB _ =>
    (match thenB with
     | .block label _ _ :: _ => origins.lookup label = none
     | _ => True) ∧
    loopExpansionFreeStmts origins thenB ∧ loopExpansionFreeStmts origins elseB
  | .block _ body _ => loopExpansionFreeStmts origins body
  | .loop _ _ _ body _ => loopExpansionFreeStmts origins body
  | .cmd _ | .exit _ _ | .typeDecl _ _ => True

/-- No expansion occurs in any statement of `ss`. -/
def loopExpansionFreeStmts (origins : LoopOrigins) : List Statement → Prop
  | [] => True
  | s :: rest => loopExpansionFreeStmt origins s ∧ loopExpansionFreeStmts origins rest

end

/-! ### Loop-elimination images

A downstream unit is the *loop-elimination image* of a source unit when it is the source
with each eliminated loop replaced by an expansion (an `if` headed by a block whose label
the origins map to that loop) and every other statement kept, with its sub-statement
lists imaged in turn (an `if` kept this way is not headed by a recorded block). -/

mutual

/-- `s'` is the loop-elimination image of the source statement `s`. -/
inductive LoopElimImageStmt (origins : LoopOrigins) : Statement → Statement → Prop where
  /-- An eliminated loop: an `if` headed by a block whose label the origins map to it. -/
  | expansion (loop : Statement) (guard : ExprOrNondet Expression) (label : String)
      (inner rest : List Statement) (md md' : Imperative.MetaData Expression)
      (h : origins.lookup label = some loop) :
      LoopElimImageStmt origins loop (.ite guard (.block label inner md' :: rest) [] md)
  | ite (guard : ExprOrNondet Expression) (t t' e e' : List Statement)
      (md : Imperative.MetaData Expression)
      (hhead : match t' with
        | .block label _ _ :: _ => origins.lookup label = none
        | _ => True) :
      LoopElimImageStmts origins t t' → LoopElimImageStmts origins e e' →
      LoopElimImageStmt origins (.ite guard t e md) (.ite guard t' e' md)
  | block (label : String) (b b' : List Statement) (md : Imperative.MetaData Expression) :
      LoopElimImageStmts origins b b' →
      LoopElimImageStmt origins (.block label b md) (.block label b' md)
  | loop (guard : ExprOrNondet Expression) (measure : Option Expression.Expr)
      (invariants : List (String × Expression.Expr)) (b b' : List Statement)
      (md : Imperative.MetaData Expression) :
      LoopElimImageStmts origins b b' →
      LoopElimImageStmt origins (.loop guard measure invariants b md)
        (.loop guard measure invariants b' md)
  | cmd (c : Command) : LoopElimImageStmt origins (.cmd c) (.cmd c)
  | exit (label : String) (md : Imperative.MetaData Expression) :
      LoopElimImageStmt origins (.exit label md) (.exit label md)
  | typeDecl (tc : TypeConstructor) (md : Imperative.MetaData Expression) :
      LoopElimImageStmt origins (.typeDecl tc md) (.typeDecl tc md)

/-- `ss'` is the loop-elimination image of the source statement list `ss`, position by
    position. -/
inductive LoopElimImageStmts (origins : LoopOrigins) :
    List Statement → List Statement → Prop where
  | nil : LoopElimImageStmts origins [] []
  | cons (s s' : Statement) (rest rest' : List Statement) :
      LoopElimImageStmt origins s s' → LoopElimImageStmts origins rest rest' →
      LoopElimImageStmts origins (s :: rest) (s' :: rest')

end

/-! ## The loop cut rule

The loop-elimination cut handler of the shared slicing replay.  Its state is the stack
of loops currently running their one sliced iteration (most recent first), each paired
with its *entry depth*: the `configNextDepth` of the configuration at the loop's cut 1,
i.e. the number of frames enclosing the loop statement.  While the loop runs its
iteration, and when it is back at its head, every configuration has at least that many
frames above its next position; a configuration with fewer means the loop was left some
other way (an `exit` out of the iteration), so its entry is stale and is popped
(`pruneActiveLoops`). -/

/-- A stack of active loops, each with its entry depth (most recent first). -/
abbrev ActiveLoops := List (Statement × Nat)

/-- Pop the active loops left at depth `d`: those whose entry depth exceeds `d`. -/
def pruneActiveLoops (d : Nat) (active : ActiveLoops) : ActiveLoops :=
  active.dropWhile fun e => decide (d < e.2)

/-- The number of frames `IConfig.focus` descends through before reaching the next
    statement's frame. -/
def configNextDepth : IConfig Expression Command → Nat
  | .seq inner _ => configNextDepth inner + 1
  | .seqs inner _ => configNextDepth inner + 1
  | .block _ _ inner => configNextDepth inner + 1
  | _ => 0

/-- The frame at depth `d` along the `IConfig.focus` path. -/
def configDescend : Nat → IConfig Expression Command → IConfig Expression Command
  | d + 1, .seq inner _ => configDescend d inner
  | d + 1, .seqs inner _ => configDescend d inner
  | d + 1, .block _ _ inner => configDescend d inner
  | _, c => c

/-- The guard decision and cut 1 for the loop `loop` about to be stepped in `c`. -/
def loopElimLoopEntry (π : String → Option Procedure) (target : AssertId Expression) (fuel : Nat)
    (c : IConfig Expression Command) (st : ReplayState Expression)
    (active : ActiveLoops) (loop : Statement) (body : List Statement)
    (env : IEnv Expression) (carried : List Expression.Ident) :
    CutStep ActiveLoops :=
  match replayRun (stepInterp (replayStepCmd π defaultMaxCallDepth) fuel c)
      { oracleConfig := .strict } st with
  | (.error _, st') => if targetFired target fuel st' then .fire st' else .stop
  | (.ok c', st') =>
    match configDescend (configNextDepth c) c' with
    | .seq _ _ =>
      -- Entered: cut 1.
      if st'.remaining.length < carried.length then .stop
      else if !allClosed (st'.remaining.take carried.length) then .stop
      else
        let envMid : IEnv Expression :=
          { env with store := env.store.bindPositional carried (st'.remaining.take carried.length) }
        let iterStart : IConfig Expression Command :=
          .seq (.block .none (.opened envMid.store) (.stmts body envMid)) [loop]
        .cut (IConfig.replaceNextStmt iterStart c) st'.usedRev.reverse
          (st'.remaining.drop carried.length) ((loop, configNextDepth c) :: active)
    | _ =>
      -- Exited (guard false): the step is taken, no cut.
      .moved c' st' active

/-- The loop cut rule, consulted before every replay step.  First the stale active loops
    are popped (`pruneActiveLoops` at the configuration's depth); then:

    * the next statement is not a loop — an ordinary step (taken by the handler itself,
      as a `moved`, when the pop changed the stack, so the popped stack is kept);
    * it is the loop on top of the stack (back at its head after its sliced iteration) —
      **cut 2**: close the current slice, pop `|M|` values into `M` (the exit state, on
      top of the post-iteration store) and take the loop-exit step; the new slice starts
      at the continuation after the loop;
    * it is any other loop (reached from outside it) — the **guard decision** by the
      replay's own loop step (a deterministic guard is evaluated, a nondeterministic one
      draws its choice from the oracle, as the downstream `if` did).  On exit, the step
      is taken and the run continues without a cut.  On entry, **cut 1**: close the
      current slice (including the guard's draw), pop `|M|` values into `M` (the mid-loop
      state) and take the loop-enter step from there; the new slice starts at that
      iteration-start configuration, and the loop is pushed on the stack with its entry
      depth. -/
def loopElimCutHandler (π : String → Option Procedure) (target : AssertId Expression) :
    CutHandler ActiveLoops := fun active fuel c st =>
  let active' := pruneActiveLoops (configNextDepth c) active
  match IConfig.focus c with
  | some (.loop guard measure invariants body md, env, _) =>
    let loop : Statement := .loop guard measure invariants body md
    let carried := Block.carriedVars body
    match active' with
    | (top, _) :: rest =>
      if top == loop then
        if st.remaining.length < carried.length then .stop
        -- the drawn values must be closed, so that the new slice's store is well-formed
        else if !allClosed (st.remaining.take carried.length) then .stop
        else
          let env' : IEnv Expression :=
            { env with
              store := env.store.bindPositional carried (st.remaining.take carried.length) }
          .cut (IConfig.replaceNextStmt (.terminal env') c) st.usedRev.reverse
            (st.remaining.drop carried.length) rest
      else loopElimLoopEntry π target fuel c st active' loop body env carried
    | [] => loopElimLoopEntry π target fuel c st active' loop body env carried
  | _ =>
    if active'.length == active.length then .step
    -- the replay's own step, taken here to keep the popped stack
    else
      match replayRun (stepInterp (replayStepCmd π defaultMaxCallDepth) fuel c)
          { oracleConfig := .strict } st with
      | (.error _, st') => if targetFired target fuel st' then .fire st' else .stop
      | (.ok c', st') => .moved c' st' active'

/-- **The loop-elimination slicer**: the slicing replay of the source from `start`,
    cutting at loop entries and exits, at fuel `replayFuelGuess`. -/
def loopElimSlice (π : String → Option Procedure) (target : AssertId Expression)
    (start : CexA Expression Command) : SliceResult :=
  sliceRun π target replayFuelGuess (loopElimCutHandler π target) [] start

end -- public section

end Core
