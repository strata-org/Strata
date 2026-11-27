/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
public import Strata.Transform.CallElim
public import Strata.DL.Imperative.StmtCFGCallSemantics
import Strata.Languages.Core.NameSets

/-! # callElim origin extractor

A deterministic extractor that recovers, for each eliminated `.call`, the call-site provenance
the transform `Core.CallElim.callElim'` consumes and does not re-emit: the callee, the call
site's arguments and left-hand sides, the parameter mapping, and the fresh names the pass
generated at that site.

The extractor traverses the program in the pass's own order (`runProgramTyped` /
`runStmtsRecTyped`) and delegates each `.call`'s state transition to the real `callElimCmd`,
recording the fresh names as the change of `genState.generated` across that call; the other
fields are read from the source statement and generate no names.  So the recorded names are the
ones the pass emits at that site.  `CounterexampleCallElimOriginTest.lean` runs both from the
same initial state and compares the fresh names.

Key definitions: `CallOrigin`, `recordCallOrigin`, `callElimOrigin'`.
-/

public section

namespace Core
namespace CallElim

open Core.Transform

/-- Provenance recorded for one eliminated `.call` site. -/
structure CallOrigin where
  /-- The callee's name, as written at the call site (`CmdExt.call procName …`). -/
  procName : String
  /-- The resolved callee procedure, as `callElimCmd` resolves it from
      `currentProgram` (`Program.Procedure.find? p procName`). -/
  callee : Procedure
  /-- The call site's input expressions, positionally aligned with the callee's
      inputs (`CallArg.getInputExprs args`). -/
  args : List Expression.Expr
  /-- The call site's output / inout target variables, positionally aligned with
      the callee's outputs (`CallArg.getLhs args`). -/
  lhs : List Expression.Ident
  /-- The callee's input parameter names (`callee.header.inputs` keys); the
      arg→param mapping is `args.zip inputParams`. -/
  inputParams : List Expression.Ident
  /-- The callee's output parameter names (`callee.header.outputs` keys); the
      lhs→param mapping is `lhs.zip outputParams`. -/
  outputParams : List Expression.Ident
  /-- The callee's declared type variables (`callee.header.typeArgs`); the
      per-call-site type substitution maps these to the freshly generated type
      variables among `freshNames` (those carrying the `freshTyVarPrefix`). -/
  typeArgs : List Lambda.TyIdentifier
  /-- Every fresh identifier `callElimCmd` generated at this call site, in
      generation order (oldest first) — the `genState.generated` delta without the names
      `CoreGenState.genAvoiding` rejected (those of the program): arg temps, out temps, old
      temps, (for a polymorphic callee) the freshened type variables, and the labels of the
      asserts and assumes it generated.  The consumers
      (`callElimFreshVars`, `RStore.dropVars`, `stmtMentionsFresh`) read the list as
      variable names; a label in it matches no variable, since generated names are
      fresh. -/
  freshNames : List Expression.Ident
  /-- The precondition-target mapping of this site: for each `assert` the pass
      generated from a non-`free` callee precondition (`createAsserts` with
      `callElimAssertPrefix`), its generated label paired with the upstream
      obligation id a replay of the original `.call` emits for that precondition
      (`defaultAssertEvents` of `Imperative.Calls.checksAtCall`: the callee's precondition
      label and the clause's site metadata at the call).
      Recorded from the real pass's output, in precondition order; empty when the number of
      generated asserts differs from the number of non-`free` preconditions, so that no
      generated label is paired with another precondition's id. -/
  preconditionTargets : List (String × Imperative.AssertId Expression) := []
  /-- The original `.call` statement at this site, verbatim (arguments and metadata). -/
  source : Statement
  /-- The statements the pass put in place of the call, verbatim:
      `argInit ++ outInit ++ oldInit ++ asserts ++ havocs ++ assumes`. -/
  expansion : List Statement := []
  /-- The number of statements of `expansion` before its havocs
      (`|argInit ++ outInit ++ oldInit ++ asserts|`): the inits and asserts. -/
  havocStart : Nat := 0
  /-- The statements following the call in its source statement list, verbatim (the
      source continuation of the call site). -/
  sourceRest : List Statement := []
  deriving Inhabited

/-- Record the provenance of a single `.call` statement, delegating the state
    transition to the real `callElimCmd`, with the type names `taken` the call's opaque types
    avoid, the names `takenVars` its temporaries avoid and the declared types `vt` of the
    variables in scope. Returns `none` for a
    non-`.call` statement (the caller then recurses, exactly as `runStmtsRecTyped` does when
    `callElimCmd` declines). -/
def recordCallOrigin (taken takenVars : Std.HashSet String) (vt : TypeSpec.TypeScopes)
    (s : Statement) :
    CoreTransformM (Option CallOrigin) := do
  match s with
  | .cmd (.call procName _ callArgs md) =>
    let lhs := Imperative.CallArg.getLhs callArgs
    let args := CallArg.getInputExprs callArgs
    let σ0 ← get
    let some p := σ0.currentProgram
      | throw (Strata.Message.fromString "recordCallOrigin: program not available")
    let some proc := Program.Procedure.find? p procName
      | throw (Strata.Message.fromFormat f!"recordCallOrigin: procedure {procName} not found")
    let genBefore := σ0.genState.generated
    -- Advance state EXACTLY as the pass does; keep the flattened statements only to
    -- read the labels of the generated precondition asserts.
    let flat ← callElimCmd taken takenVars vt s
    let σ1 ← get
    let genAfter := σ1.genState.generated
    -- `generated` is cons-prepended (newest first). The delta is the length-
    -- difference prefix of `genAfter`; reverse it to generation order. The generator also logs
    -- the names `CoreGenState.genAvoiding` drew and rejected, the ones in `takenVars` (names of
    -- the program); only the names it returned are the call's temporaries.
    let newCount := genAfter.length - genBefore.length
    let fresh := (genAfter.take newCount).reverse.filter fun n => !takenVars.contains n.name
    let generatedLabels : List String := (flat.getD []).filterMap fun st =>
      match st with
      | .cmd (.cmd (.assert label _ _)) =>
        if label.startsWith callElimAssertPrefix then some label else none
      | _ => none
    let upstreamIds : List (Imperative.AssertId Expression) :=
      ((Imperative.Calls.checksAtCall md proc.spec.preconditions).filter
          (fun (_, check) => check.attr != .Free)).map
        fun (label, check) => { label := label, md := check.md }
    return .some {
      procName := procName
      callee := proc
      args := args
      lhs := lhs
      inputParams := proc.header.inputs.keys
      outputParams := proc.header.outputs.keys
      typeArgs := proc.header.typeArgs
      freshNames := fresh
      preconditionTargets :=
        if generatedLabels.length == upstreamIds.length then generatedLabels.zip upstreamIds else []
      source := s
      expansion := flat.getD []
      havocStart := ((flat.getD []).takeWhile fun st =>
        match st with
        | .cmd (.cmd (.init _ _ _ _)) | .cmd (.cmd (.assert _ _ _)) => true
        | _ => false).length }
  | _ => return .none

/-- Origin-recording traversal of a statement list, mirroring `runStmtsRecTyped`'s
    structure verbatim (same head-before-tail source order, same recursion into
    `block`/`ite`/`loop` with a new scope, same pass-through for `typeDecl`/`exit`, the same
    declared types `vt` before each statement) so the fresh counter advances in the
    identical order to the real pass. Threads and returns the accumulated origins in
    traversal order. -/
def recordStmtsRec (taken takenVars : Std.HashSet String) (vt : TypeSpec.TypeScopes)
    (ss : List Statement) : CoreTransformM (List CallOrigin) := do
  match ss with
  | [] => return []
  | s :: ss' =>
    let (headOrigins, sres) ← (do
      match ← recordCallOrigin taken takenVars vt s with
      | .some o => return ([{ o with sourceRest := ss' }], o.expansion)
      | .none =>
        match s with
        | .cmd _ => return ([], [s])
        | .block _ b _ => return (← recordStmtsRec taken takenVars (vt.push .empty) b, [s])
        | .ite _ thenb elseb _ => do
          let o1 ← recordStmtsRec taken takenVars (vt.push .empty) thenb
          let o2 ← recordStmtsRec taken takenVars (vt.push .empty) elseb
          return (o1 ++ o2, [s])
        | .loop _ _ _ body _ => return (← recordStmtsRec taken takenVars (vt.push .empty) body, [s])
        | .typeDecl _ _ => return ([], [s])
        | .exit _ _ => return ([], [s]))
    let tailOrigins ← recordStmtsRec taken takenVars (vt.addInits sres) ss'
    return headOrigins ++ tailOrigins

/-- Program-level origin extractor: a sibling of `callElim'`
    ([CallElim.lean](../../Transform/CallElim.lean)) that walks every
    procedure body exactly as `runProgramTyped (targetProcList := .none)` does —
    setting `currentProgram`/`currentProcedureName` identically, in the same
    declaration order, a CFG body through `runCFGCmdsTyped` with `callElimCommand` as
    `callElim'` does — but records a `CallOrigin` per `.call` site of a structured body
    (via `recordStmtsRec`) instead of rebuilding the program. Returns the origins in
    traversal order. -/
def callElimOrigin' (p : Program) : CoreTransformM (List CallOrigin) := do
  let taken := p.typeNamesWithPrefix callElimTyPrefix
  let takenVars := p.varNames.insertMany (p.declaredNames ++ p.funcNames)
  modify (fun σ => { σ with currentProgram := .some p })
  let mut origins : List CallOrigin := []
  for decl in p.decls do
    match decl with
    | .proc proc _md =>
      modify (fun σ => { σ with currentProcedureName := .some proc.header.name.1 })
      match proc.body with
      | .structured ss _ =>
        let procOrigins ← recordStmtsRec taken takenVars (TypeSpec.procBodyScopes [] proc) ss
        origins := origins ++ procOrigins
      | .cfg g _ =>
        -- The pass eliminates the calls of a CFG body block by block (`runCFGCmdsTyped` with
        -- `callElimCommand`); running it here advances the fresh counter as the pass does, so
        -- the origins of the procedures after this one record the pass's names. A CFG body's
        -- calls get no origin: the back-link lifts through structured bodies only.
        let _ ← runCFGCmdsTyped (callElimCommand taken takenVars)
          ((TypeSpec.procBodyScopes [] proc).addCFGInits g) g
      | .abstract => pure ()
    | _ => pure ()
  modify (fun σ => { σ with currentProcedureName := .none })
  return origins

end CallElim
end Core

end -- public section
