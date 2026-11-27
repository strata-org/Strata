/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.Model
public import Strata.Languages.Core.Counterexample.ModelToValuation
public import Strata.Languages.Core.Counterexample.ValuationToRun
public import Strata.Languages.Core.Counterexample.BackLinkCallElimOrigin
public import Strata.Languages.Core.Counterexample.BackLinkChainReplay
import Strata.DL.Imperative.Counterexample.Tactics

/-! # `callElim` back-link support: provenance, configuration mapping, slicing

Support for the `(a) → (a)` back-link `callElimBackLink` (`BackLinkPhases`) of
the call-elimination phase `callElimPipelinePhase`
([CallElim.lean](Strata/Transform/CallElim.lean)).  Level `(a)` is a run of the
program: a `CexA`, a start configuration replayed with an oracle of nondeterministic
choices.

## What the pass abstracts

Call elimination replaces each `.call` by `argInit ++ outInit ++ oldInit ++ asserts ++
havocs ++ assumes`: the callee's contract instead of its body.  The downstream
counterexample picks each call's outputs freely (the havocs), and nothing says that
running the callee from the call's pre-state returns them, unless the callee is opaque
(`Body.isOpaque`): callers know an opaque callee only through its contract, so its expansion
is its call semantics and the source replay runs the call as its contract.  So every
eliminated call to a callee that is not opaque on the failing path is a *slicing point*: the
lifted counterexample is a chain of slices, one per stretch between such calls, with an open
reachability question at each of them.

## Provenance

The pass keeps no back-reference from an expansion to its call.  The deterministic
sibling extractor `Core.CallElim.callElimOrigin'`
([BackLinkCallElimOrigin.lean](Strata/Languages/Core/Counterexample/BackLinkCallElimOrigin.lean))
re-runs the pass's own per-call step and records, per call site, a `CallOrigin`: the
original call statement, its expansion, the position of the havocs in it, the fresh
names, and the precondition-target mapping (generated assert label → callee
precondition id).

## Oracle alignment

The inits, asserts and assumes of an expansion draw nothing from the oracle; the
havocs draw exactly `|lhs|` values; everything outside expansions is copied verbatim.
So a replay of the *source* consumes the downstream oracle identically, except that at
each eliminated call it must take the call's `|lhs|` outputs from the oracle instead of
running the callee.  A call to an opaque callee does exactly that when it runs as its contract:
it havocs the callee's `|lhs|` output parameters, in order, with the next values of the oracle.

## The pieces in this file

* `callElimUpstreamTarget` — the target id upstream: a generated precondition assert
  maps to the id the original call's replay emits for that precondition.
* `uncallElimConfig` — maps a configuration of the pass's output to the source: every
  expansion becomes its call again, a start inside an expansion maps to the call (inits,
  asserts) or right after it (assumes), a start between the havocs has no counterpart,
  and the fresh variables are dropped from the stores.  It is the identity outside
  expansions.
* `callElimCutHandler` / `callElimSlice` — the slicing replay of the source
  (`sliceRun`, `BackLinkChainReplay.lean`) cutting at eliminated calls: first the
  callee precondition check (the code of `replayStepCmd`'s `.call` entry,
  `callElimEntry`), whose firing is a claim at the call entry; otherwise the cut, which
  pops the outputs from the oracle, binds them to the lhs and continues after the call.
  Calls the pass did not eliminate are executed for real.

* `expansionFreeStmts` / `CallElimImageStmts` — the downstream units on which
  `uncallElimConfig` is the identity, and the call-elimination image of a source unit,
  whose top it maps back to the top of the source unit
  (`BackLinkCallElimProps`).

Key definitions: `callElimUpstreamTarget`, `uncallElimConfig`, `CallElimImageStmts`,
`callElimCutHandler`, `callElimSlice`.

## Validity

`ValidOutcome` validates claims under the program's callee table `π`, the same `π` the
slicing and chain replays use, so a claim whose failing path runs through a real call
validates.  The back-link's head is the top of the source unit by construction, and a
claim is only returned after the chain replay's `replayCandidate` re-validation.
-/

namespace Core

open _root_.Lambda Imperative
open Core.CallElim (CallOrigin)

public section

/-- Map a downstream obligation id to the upstream id of the call-elimination
    source, in two cases:
    * **Mapped**: `target.label` is the generated label of a precondition check of some
      origin, recorded with the upstream id `u` (`CallOrigin.preconditionTargets`): the
      result is `u`, the id the original `.call` emits for that precondition (the callee's
      precondition label and the clause's site metadata at the call).  Several call sites
      may share `u`.
    * **Not generated**: `target.label` is the generated label of no origin's precondition
      check: the result is `target`. -/
def callElimUpstreamTarget (origins : List CallOrigin)
    (target : Imperative.AssertId Expression) : Imperative.AssertId Expression :=
  match origins.findSome? (fun o => o.preconditionTargets.lookup target.label) with
  | some upstream => upstream
  | none => target

/-! ## Mapping a downstream configuration upstream (`uncallElimConfig`)

The downstream program has each eliminated call replaced by its expansion
(`CallOrigin.expansion`, spliced into the enclosing statement list); everything else
is verbatim.  `uncallElimConfig` maps a configuration of the downstream program to
the corresponding configuration of the source: every recognized expansion becomes the
original call again, and the fresh variables the pass introduced are dropped from
every store. -/

/-- Every fresh variable the pass introduced, over all call sites. -/
def callElimFreshVars (origins : List CallOrigin) : List Expression.Ident :=
  origins.flatMap (·.freshNames)

/-- An environment with the variables `fresh` removed from its store. -/
def dropFreshEnv (fresh : List Expression.Ident) (env : IEnv Expression) : IEnv Expression :=
  { env with store := .ofStore (RStore.dropVars fresh env.store.get) }

/-- The call site whose (non-empty) expansion starts the statement list `ss`. -/
def expansionAt? (origins : List CallOrigin) (ss : List Statement) : Option CallOrigin :=
  origins.find? fun o => !o.expansion.isEmpty && o.expansion.isPrefixOf ss

mutual

/-- A statement with every recognized expansion in its sub-statement lists replaced by
    its original call. -/
def uncallElimStmt (origins : List CallOrigin) : Statement → Statement
  | .block label body md => .block label (uncallElimStmts origins 0 body) md
  | .ite cond thenB elseB md =>
    .ite cond (uncallElimStmts origins 0 thenB) (uncallElimStmts origins 0 elseB) md
  | .loop guard measure invariants body md =>
    .loop guard measure invariants (uncallElimStmts origins 0 body) md
  | .cmd c => .cmd c
  | .exit label md => .exit label md
  | .typeDecl tc md => .typeDecl tc md

/-- A statement list with every recognized expansion replaced by its original call.
    `skip` statements are dropped first (the rest of an expansion just replaced). -/
def uncallElimStmts (origins : List CallOrigin) (skip : Nat) :
    List Statement → List Statement
  | [] => []
  | s :: rest =>
    match skip with
    | k + 1 => uncallElimStmts origins k rest
    | 0 =>
      match expansionAt? origins (s :: rest) with
      | some o => o.source :: uncallElimStmts origins (o.expansion.length - 1) rest
      | none => uncallElimStmt origins s :: uncallElimStmts origins 0 rest

end

/-- Where a statement list starts strictly inside an expansion: the call site and the
    number `k ≥ 1` of its statements already executed.  Recognition is by the recorded
    call-site data, not by the statements alone: the list must be `o.expansion.drop k`
    followed by a continuation that maps upstream (`uncallElimStmts`) to exactly the
    call's recorded source continuation `o.sourceRest`.  A source statement list that
    merely starts like the tail of an expansion (e.g. a source `havoc x` equal to one of
    the expansion's havocs) is continued by something else and is not recognized. -/
def midExpansion? (origins : List CallOrigin) (ss : List Statement) :
    Option (CallOrigin × Nat) :=
  origins.findSome? fun o =>
    ((List.range o.expansion.length).filter (· ≥ 1)).findSome? fun k =>
      if (o.expansion.drop k).isPrefixOf ss &&
          uncallElimStmts origins 0 (ss.drop (o.expansion.length - k)) == o.sourceRest
      then some (o, k) else none

/-- Does the statement mention (define, assign or read) one of the variables `fresh`? -/
def stmtMentionsFresh (fresh : List Expression.Ident) (s : Statement) : Bool :=
  match s with
  | .cmd (.cmd c) => (Cmd.definedVars c ++ Cmd.modifiedVars c ++ Cmd.getVars c).any (· ∈ fresh)
  | _ => false

/-- How a statement list that starts inside an expansion maps upstream. -/
inductive MidPosition where
  /-- In the inits or asserts: upstream is at the call (before it); the list is the
      call followed by the mapped rest. -/
  | atCall (upstream : List Statement)
  /-- In the assumes: upstream is right after the call; the list is the mapped rest. -/
  | afterCall (upstream : List Statement)
  /-- In the havocs (some outputs drawn, some not): no upstream counterpart. -/
  | inHavocs

/-- Classify a list that starts `k` statements into the expansion of `o`, and map it. -/
def midPosition (origins : List CallOrigin) (o : CallOrigin) (k : Nat)
    (ss : List Statement) : MidPosition :=
  let tail := uncallElimStmts origins 0 (ss.drop (o.expansion.length - k))
  if k ≤ o.havocStart then .atCall (o.source :: tail)
  else if o.havocStart + o.lhs.length ≤ k then .afterCall tail
  else .inHavocs

/-- **Map a downstream configuration upstream.**  Frames outside expansions map to
    themselves (with their statement lists un-eliminated); a frame starting inside an
    expansion maps to the call (inits/asserts) or to just after it (assumes); a start
    inside the havocs has no upstream counterpart (`none`).  Every store loses the
    pass's fresh variables, and every scope frame becomes an embedded frame
    (`defined = none`). -/
def uncallElimConfig (origins : List CallOrigin) :
    IConfig Expression Command → Option (IConfig Expression Command)
  | .stmt s env =>
    let env' := dropFreshEnv (callElimFreshVars origins) env
    -- A lone statement has no continuation to check, so it is attributed to a call site
    -- only if it mentions that site's fresh variables; one that equals an expansion
    -- statement but mentions none of them (a havoc or assume over the call's own
    -- variables) is ambiguous and has no upstream image.
    match origins.find? (fun o => s ∈ o.expansion && stmtMentionsFresh o.freshNames s) with
    | some o =>
      match o.expansion.idxOf? s with
      | some k => if k < o.havocStart then some (.stmt o.source env') else none
      | none => none
    | none =>
      if origins.any (fun o => s ∈ o.expansion) then none
      else some (.stmt (uncallElimStmt origins s) env')
  | .stmts ss env =>
    let env' := dropFreshEnv (callElimFreshVars origins) env
    match midExpansion? origins ss with
    | none => some (.stmts (uncallElimStmts origins 0 ss) env')
    | some (o, k) =>
      match midPosition origins o k ss with
      | .atCall up => some (.stmts up env')
      | .afterCall up => some (.seq (.terminal env') up)
      | .inHavocs => none
  | .terminal env => some (.terminal (dropFreshEnv (callElimFreshVars origins) env))
  | .exiting label env =>
    some (.exiting label (dropFreshEnv (callElimFreshVars origins) env))
  | .seq (.stmt s env) rest =>
    let env' := dropFreshEnv (callElimFreshVars origins) env
    match midExpansion? origins (s :: rest) with
    | none =>
      match expansionAt? origins (s :: rest) with
      | some o =>
        some (.seq (.stmt o.source env')
          (uncallElimStmts origins 0 (rest.drop (o.expansion.length - 1))))
      | none => some (.seq (.stmt (uncallElimStmt origins s) env') (uncallElimStmts origins 0 rest))
    | some (o, k) =>
      match midPosition origins o k (s :: rest) with
      | .atCall (call :: up) => some (.seq (.stmt call env') up)
      | .atCall [] => none
      | .afterCall up => some (.seq (.terminal env') up)
      | .inHavocs => none
  | .seq (.terminal env) rest =>
    let env' := dropFreshEnv (callElimFreshVars origins) env
    match midExpansion? origins rest with
    | none => some (.seq (.terminal env') (uncallElimStmts origins 0 rest))
    | some (o, k) =>
      match midPosition origins o k rest with
      | .atCall up => some (.seq (.terminal env') up)
      | .afterCall up => some (.seq (.terminal env') up)
      | .inHavocs => none
  | .seq inner rest =>
    (uncallElimConfig origins inner).map fun inner' =>
      .seq inner' (uncallElimStmts origins 0 rest)
  | .seqs inner k => (uncallElimConfig origins inner).map fun inner' => .seqs inner' k
  | .block label fr inner =>
    (uncallElimConfig origins inner).map fun inner' =>
      .block label { parent := .ofStore (RStore.dropVars (callElimFreshVars origins) fr.parent.get),
                     defined := none } inner'

/-! ### Expansion-free statements -/

mutual

/-- No sub-list of `s`'s statement lists starts an expansion. -/
def expansionFreeStmt (origins : List CallOrigin) : Statement → Prop
  | .block _ body _ => expansionFreeStmts origins body
  | .ite _ thenB elseB _ => expansionFreeStmts origins thenB ∧ expansionFreeStmts origins elseB
  | .loop _ _ _ body _ => expansionFreeStmts origins body
  | .cmd _ | .exit _ _ | .typeDecl _ _ => True

/-- No suffix of `ss`, and no statement list nested in it, starts an expansion. -/
def expansionFreeStmts (origins : List CallOrigin) : List Statement → Prop
  | [] => True
  | s :: rest =>
    expansionAt? origins (s :: rest) = none ∧ expansionFreeStmt origins s ∧
      expansionFreeStmts origins rest

end

/-! ### The top-level downstream start

A downstream unit is the *call-elimination image* of a source unit when it is the source
with each eliminated call replaced by its recorded expansion (recognized there by
`expansionAt?`) and every other statement kept, with its sub-statement lists imaged in
turn. -/

mutual

/-- `s'` is the call-elimination image of the source statement `s`. -/
inductive CallElimImageStmt (origins : List CallOrigin) : Statement → Statement → Prop where
  | block (label : String) (b b' : List Statement) (md : Imperative.MetaData Expression) :
      CallElimImageStmts origins b b' →
      CallElimImageStmt origins (.block label b md) (.block label b' md)
  | ite (cond : ExprOrNondet Expression) (t t' e e' : List Statement)
      (md : Imperative.MetaData Expression) :
      CallElimImageStmts origins t t' → CallElimImageStmts origins e e' →
      CallElimImageStmt origins (.ite cond t e md) (.ite cond t' e' md)
  | loop (guard : ExprOrNondet Expression) (measure : Option Expression.Expr)
      (invariants : List (String × Expression.Expr)) (b b' : List Statement)
      (md : Imperative.MetaData Expression) :
      CallElimImageStmts origins b b' →
      CallElimImageStmt origins (.loop guard measure invariants b md)
        (.loop guard measure invariants b' md)
  | cmd (c : Command) : CallElimImageStmt origins (.cmd c) (.cmd c)
  | exit (label : String) (md : Imperative.MetaData Expression) :
      CallElimImageStmt origins (.exit label md) (.exit label md)
  | typeDecl (tc : TypeConstructor) (md : Imperative.MetaData Expression) :
      CallElimImageStmt origins (.typeDecl tc md) (.typeDecl tc md)

/-- `ss'` is the call-elimination image of the source statement list `ss`. -/
inductive CallElimImageStmts (origins : List CallOrigin) :
    List Statement → List Statement → Prop where
  | nil : CallElimImageStmts origins [] []
  /-- An eliminated call: its expansion, recognized at this position. -/
  | call (o : CallOrigin) (rest post : List Statement) (hne : o.expansion ≠ [])
      (hat : expansionAt? origins (o.expansion ++ post) = some o) :
      CallElimImageStmts origins rest post →
      CallElimImageStmts origins (o.source :: rest) (o.expansion ++ post)
  /-- Any other statement, at a position where no expansion is recognized. -/
  | stmt (s s' : Statement) (rest rest' : List Statement)
      (hat : expansionAt? origins (s' :: rest') = none) :
      CallElimImageStmt origins s s' → CallElimImageStmts origins rest rest' →
      CallElimImageStmts origins (s :: rest) (s' :: rest')

end

/-! ## The call-elimination slicer

Replays the *source* unit with the downstream oracle and cuts at every eliminated call
(`sliceRun` with `callElimCutHandler`).  Between eliminated calls the source and the
downstream program draw the oracle identically; at an eliminated call the downstream
program draws exactly the call's `|lhs|` output values (its havocs), which the cut pops
and binds to the lhs targets. -/

/-- The call site an eliminated `.call` command belongs to: the origin recording this
    exact statement (callee name, type arguments, arguments and metadata). -/
def eliminatedCallOrigin? (origins : List CallOrigin) (procName : String)
    (tyArgs : Option (List Expression.Ty)) (args : List (CallArg Expression))
    (md : Imperative.MetaData Expression) : Option CallOrigin :=
  origins.find? fun o => decide (o.source = .cmd (.call procName tyArgs args md))

/-- The entry part of a `.call` step, as `Calls.stepCmd`'s `.call` arm runs it: evaluate the
    input actuals (bounded, at `fuel`) and check their arity against the callee's inputs, read
    the out-only actuals and check their arity, build the callee's entry frame
    (`Calls.callEntryStore`), and emit the callee's non-`free` preconditions as assert events at
    that frame, with the call metadata `md` as their site (`Imperative.Calls.checksAtCall`). -/
def callElimEntry {m : Type → Type} [Monad m] [InterpEffects Expression m]
    [MonadExcept StopReason m] (procName : String) (p : Procedure) (fuel : Nat)
    (env : IEnv Expression) (args : List (CallArg Expression))
    (md : Imperative.MetaData Expression) : m Unit := do
  let some inputVals :=
      evalBoundedList fuel env.factory env.store.get (Calls.getInputExprs args)
    | throw .expressionDidNotEvaluate
  if inputVals.length ≠ (ProcedureHeader.inputParams (P := Expression) p.header).length
  then throw (.programCallInputArityMismatch procName)
  let some outOnlyVals := Calls.readVarList env.store.get (Imperative.CallArg.getOutArgs args)
    | throw (.programCallLhsUndefined procName)
  if outOnlyVals.length ≠ (Calls.outputOnlyParams (P := Expression) p.header).length then
    throw (.programCallOutputArityMismatch procName)
  (Calls.rDefaultAssertEvents env.factory (Calls.callEntryStore p inputVals outOnlyVals)
      (Imperative.Calls.checksAtCall md p.spec.preconditions)).forM
    (InterpEffects.emit (P := Expression))

/-- The choices of a callee run that aims at the call's outputs `values` (the values the
    downstream run gives the call's targets): a choice of a type some value of `values` has
    takes the first such value, any other the default value of its type (`defaultValueIn`). -/
def callOutputDefaults (values : List Expression.Expr) (F : @Lambda.Factory CoreLParams)
    (_ : RStore Expression) (ty : Expression.Ty) : Option Expression.Expr :=
  (values.find? fun v => valueHasType F v ty).orElse fun _ =>
    (Lambda.LTy.toMonoType? ty).bind (defaultValueIn F)

/-- The real run of the call at `c` whose callee's choices aim at the call's outputs
    `values` (`callOutputDefaults`), from the replay state `st` with its oracle set aside: the
    configuration after the call and the state, the oracle `remaining` restored, when the run
    succeeds without firing the target and binds each target `lhs` to its value of `values`
    (up to metadata). The values the callee drew are recorded in the state's `usedRev`, so a
    replay of the recorded oracle runs the callee as here. -/
def callTowardOutputs (π : String → Option Procedure) (target : AssertId Expression)
    (fuel : Nat) (c : IConfig Expression Command) (st : ReplayState Expression)
    (lhs : List Expression.Ident) (values remaining : List Expression.Expr) :
    Option (IConfig Expression Command × ReplayState Expression) :=
  match replayRun (stepInterp (replayStepCmd π defaultMaxCallDepth) fuel c)
      { oracleConfig := .withDefaults (callOutputDefaults values),
        interruptOn := targetInterrupt target fuel } { st with remaining := [] } with
  | (.ok c', st') =>
    if (lhs.zip values).all (fun (x, v) =>
        (c'.getEnv.store.get x).any (InterpLang.eqModuloMeta · v)) then
      some (c', { st' with remaining := remaining })
    else none
  | (.error _, _) => none

/-- The callElim cut rule, consulted before every replay step:

    * the next command is not an eliminated call (including a call the pass did not
      eliminate) — an ordinary step;
    * it is an eliminated call to an opaque callee (`Body.isOpaque`) — an ordinary step: the
      replay's stepper (`replayStepCmd`, in `CallMode.contract`) runs the call as its
      contract, which is the reference semantics of the call (`call_abstract_sem`) and what
      the pass put in its place: the preconditions checked at the callee's entry, the outputs
      havocked with the next `|lhs|` values of the oracle (the values the downstream run gave
      the expansion's havocs), the postconditions assumed;
    * it is an eliminated call to any other callee — first the **precondition check**: the
      call's entry (`callElimEntry`, the code `replayStepCmd`'s `.call` arm runs: evaluate the
      arguments, build the callee's entry frame, emit its non-free preconditions); if the
      target fires there, that is the claim.  Otherwise the call's `|lhs|` outputs are the
      next values of the oracle, and the **real call** is tried first: the callee runs with
      its choices aimed at those outputs (`callTowardOutputs`); when it returns them, the
      replay moves past the call without cutting, the oracle past the outputs.  Otherwise
      the **cut**: pop the outputs from the oracle, bind them to the lhs targets (out and
      inout alike, as the call's write-back does), and continue from the configuration right
      after the call. -/
def callElimCutHandler (π : String → Option Procedure) (target : AssertId Expression)
    (origins : List CallOrigin) : CutHandler Unit := fun _ fuel c st =>
  match IConfig.nextCmd? c with
  | some (.call procName tyArgs args md, env) =>
    match eliminatedCallOrigin? origins procName tyArgs args md with
    | none => .step
    | some _ =>
      match π procName with
      | none => .stop
      | some p =>
        if p.body.isOpaque then .step else
        match replayRun (callElimEntry procName p fuel env args md)
            { oracleConfig := .strict } st with
        | (.error _, st') => if targetFired target fuel st' then .fire st' else .stop
        | (.ok (), st') =>
          if targetFired target fuel st' then .fire st'
          else
            let lhs := Imperative.CallArg.getLhs args
            if st.remaining.length < lhs.length then .stop
            -- the drawn values must be closed for the new slice's store to be (`CfgWF`)
            else if !allClosed (st.remaining.take lhs.length) then .stop
            else
              let values := st.remaining.take lhs.length
              match callTowardOutputs π target fuel c st lhs values
                  (st.remaining.drop lhs.length) with
              | some (c', st'') => .moved c' st'' ()
              | none =>
                let env' : IEnv Expression :=
                  { env with store := env.store.bindPositional lhs values }
                .cut (IConfig.replaceNextStmt (.terminal env') c) st.usedRev.reverse
                  (st.remaining.drop lhs.length) ()
  | _ => .step

/-- **The call-elimination slicer**: the slicing replay of the source from `start`
    (a configuration of the source unit and an oracle), cutting at eliminated calls,
    at fuel `replayFuelGuess`. -/
def callElimSlice (π : String → Option Procedure) (target : AssertId Expression)
    (origins : List CallOrigin) (start : CexA Expression Command) : SliceResult :=
  sliceRun π target replayFuelGuess (callElimCutHandler π target origins) () start

end -- public section

end Core
