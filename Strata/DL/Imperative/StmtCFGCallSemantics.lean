/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CFGSemantics
public import Strata.DL.Imperative.CmdCallFormals
public import Strata.DL.Imperative.StmtSemantics

/-! # Reference semantics of procedure calls, over any `PureExpr`

This file gives the event-producing meaning of `CmdExt P` — a base command or a
procedure call — for any expression language `P`.

A call `call n args` to a procedure `p = π n` runs to completion in one command
step:
- *Entry* (`Calls.CallEntry`): evaluate the input and inout arguments in the
  caller's store, read the caller's `out` variables, and build a fresh callee
  frame binding the input formals and the output-only formals.  Every inout
  formal `g` is also bound under `HasOldIdent.mkOld g` to its entry value (its
  *old snapshot*), so that postconditions can refer to it.
- *Precondition events*: each non-free precondition is emitted as an assertion
  event, evaluated in the entry frame.
- *Body*: the body runs from the entry frame until it terminates, emitting its own
  events.
- *Postcondition events*: each non-free postcondition is emitted as an assertion
  event, evaluated in the callee's final frame.
- *Exit* (`Calls.CallExit`): read the output formals in the final frame and write
  them back to the caller's `out`/`inout` variables.
The call's trace is the precondition events, then the body events, then the
postcondition events.

`EvalCmdExtE` (one command) and `BigStepE` (one procedure body) are mutually
inductive: a call's `EvalCmdExtE.call_sem` derivation contains a `BigStepE`
derivation of the callee body. A structured body is a multi-step run of
`StepStmtE`; a CFG body is a multi-step run of `StepCFGE`. Both relations obtain
their execution environment from their configurations, and both evaluate commands
with `EvalCmdExtE` itself. Nested calls therefore nest derivations.

`EvalCmdExtContractE` is the modular alternative for a call: it uses the same
entry and exit, but replaces the body by havocking the output formals
(`Calls.HavocVars`) and emitting every postcondition as an assumption event
(`Calls.assumeEvents`).

The CFG and Kleene event relations (`StepCFGE`, `StepKleeneE`) are parameterized
by a command relation.  `CallAwareSemantics.lean` instantiates them with
`EvalCmdExtE`, so a call in a CFG block or a Kleene command runs its callee body,
structured or CFG, through `BigStepE`, with no CFG- or Kleene-specific call rule. -/

namespace Imperative

public section

namespace Calls

variable {P : PureExpr}

/-- Nondeterministically update the existing slots `xs`, each to a value of its
    stored runtime type. -/
inductive HavocVars [HasVal P] :
    P.Factory → SemanticStore P → List P.Ident → SemanticStore P → Prop where
  | update_none :
    HavocVars f σ [] σ
  | update_some :
    UpdateState P σ x v σ' →
    HasVal.valueOfStoredTy (P := P) f σ x v →
    HavocVars f σ' xs σ'' →
    HavocVars f σ (x :: xs) σ''

/-- Extend a store with `old` snapshots: every `g ∈ snapshot` gains a binding of
    `HasOldIdent.mkOld g` to `g`'s current value.  All other lookups, `g` itself
    included, are unchanged. -/
@[expose] def withOldSnapshots [DecidableEq P.Ident] [HasOldIdent P]
    (snapshot : List P.Ident) (σ : SemanticStore P) : SemanticStore P :=
  fun id =>
    match snapshot.find? (fun g => HasOldIdent.mkOld g == id) with
    | some g => σ g
    | none   => σ id

variable [DecidableEq P.Ident] [HasOldIdent P]
  {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]

/-- Initialize a callee-local frame without colliding with caller names: starting
    from the empty store, the input formals are bound to `inputVals`, the
    output-only formals to `outOnlyVals`, and every inout formal is snapshotted
    under its `old` name. -/
@[expose] def InitCallFrame
    (p : Procedure P (CmdExt P) Hdr) (inputVals outOnlyVals : List P.Expr)
    (σAO : SemanticStore P) : Prop :=
  ∃ σA σIO,
    InitStates emptyStore (ProcedureHeader.inputParams (P := P) p.header) inputVals σA ∧
    InitStates σA (outputOnlyParams (P := P) p.header) outOnlyVals σIO ∧
    σAO = withOldSnapshots (inoutParams (P := P) p.header) σIO

/-- Capture the non-free specification clauses `checks` as assertion events at the
    semantic snapshot `(fac, σ)`.  Free clauses are not call-site obligations. -/
@[expose] def defaultAssertEvents
    (fac : P.Factory) (σ : SemanticStore P) (checks : ListMap String (Check P)) : Trace P :=
  checks.toList.filterMap fun (label, check) =>
    if check.attr = .Default then
      some (.assert { factory := fac, store := σ, label := label, expr := check.expr,
                      metadata := check.md })
    else
      none

/-- Capture every specification clause in `checks` as an assumption event at the
    semantic snapshot `(fac, σ)`, free clauses included: a caller relying on a
    contract assumes all of the callee's postconditions. -/
@[expose] def assumeEvents
    (fac : P.Factory) (σ : SemanticStore P) (checks : ListMap String (Check P)) : Trace P :=
  checks.toList.map fun (label, check) =>
    .assume { factory := fac, store := σ, label := label, expr := check.expr,
              metadata := check.md }

section Entry

variable [HasFvar P] [HasFvars P] [HasVal P]

/-- Shared prologue of the call rule: evaluate the input and inout arguments, read
    the caller's `out` variables, and build the collision-free callee frame. -/
@[expose] def CallEntry (fac : P.Factory) (σ : SemanticStore P)
    (p : Procedure P (CmdExt P) Hdr) (callArgs : List (CallArg P)) (σAO : SemanticStore P) :
    Prop :=
  ∃ inputVals outOnlyVals,
    EvalExpressions fac σ (getInputExprs callArgs) inputVals ∧
    ReadValues fac σ (CallArg.getOutArgs callArgs) outOnlyVals ∧
    InitCallFrame p inputVals outOnlyVals σAO

/-- Shared epilogue of the call rule: read the callee's output formals in its final
    store and write them back positionally to the caller's `out`/`inout` variables,
    which must be distinct. -/
@[expose] def CallExit (fac : P.Factory) (σ : SemanticStore P)
    (p : Procedure P (CmdExt P) Hdr) (callArgs : List (CallArg P))
    (σEnd σ' : SemanticStore P) : Prop :=
  (CallArg.getLhs callArgs).Nodup ∧
  ∃ outputVals,
    ReadValues fac σEnd (ProcedureHeader.outputParams (P := P) p.header) outputVals ∧
    UpdateStates σ (CallArg.getLhs callArgs) outputVals σ'

end Entry

end Calls

/-! ## Call-aware command semantics -/

variable {P : PureExpr}
  [DecidableEq P.Ident] [HasOldIdent P]
  {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]
  [HasBool P] [HasBoolOps P] [HasFvar P] [HasFvars P]

mutual

/-- Event-producing execution of a procedure body, structured or CFG, from its
    entry environment to normal termination.  Inner scoping does not leak past the
    call: variables initialized by the body are dropped from the final store. -/
inductive BigStepE
    (π : String → Option (Procedure P (CmdExt P) Hdr)) :
    Body P (CmdExt P) → Env P → SemanticStore P → Trace P → Prop where
  /-- A structured body runs wrapped in `Stmt.block "" ss #[]`, which scopes
      `init`s and catches `exit ""`. -/
  | structured :
      ReflTransTrace (StepStmtE P (EvalCmdExtE π))
        (.stmt (Stmt.block "" ss #[]) ρ)
        emitted
        (.terminal ρ') →
      ----
      BigStepE π (.structured ss) ρ ρ'.store emitted

  /-- A CFG body runs from its entry block to `finish`. The CFG program and
      environment are carried by each `CFGConfig`, so the nested relation captures
      only the globally fixed command evaluator `EvalCmdExtE π`. The final store is
      projected through the entry store to drop body-local variables. -/
  | cfg :
      ReflTransTrace (StepCFGE P (EvalCmdExtE π))
        (.atBlock g g.entry ρ)
        emitted
        (.terminal ρ') →
      ----
      BigStepE π (.cfg g) ρ (projectStore ρ.store ρ'.store) emitted

/-- Event-producing command semantics of `CmdExt P`.  Base commands delegate to
    `EvalCmdE`.  A call emits its non-free preconditions as assertions at the
    callee entry frame, executes its body from that frame, and emits its non-free
    postconditions as assertions at the callee's final frame. The call runs its
    body and interprets each contract clause with the active factory `fac`. -/
inductive EvalCmdExtE
    (π : String → Option (Procedure P (CmdExt P) Hdr)) :
    P.Factory → SemanticStore P → CmdExt P → SemanticStore P → Trace P → Prop where
  | cmd_sem {fac σ c σ' emitted} :
      EvalCmdE (P := P) fac σ c σ' emitted →
      ----
      EvalCmdExtE π fac σ (.cmd c) σ' emitted

  /-- Arguments are matched positionally in three alignments:
      `Calls.getInputExprs callArgs` ↔ `ProcedureHeader.inputParams p.header`;
      `CallArg.getLhs callArgs` ↔ `ProcedureHeader.outputParams p.header`; and
      `CallArg.getOutArgs callArgs` ↔ `Calls.outputOnlyParams p.header`.  The third
      alignment follows from the second because every inout formal is passed as
      `.inoutArg`. -/
  -- TODO: Instantiate procedure type variables for polymorphic calls.
  | call_sem {σ n p callArgs σ' σ_final bodyEvents md fac σAO} :
      π n = .some p →
      Calls.CallEntry fac σ p callArgs σAO →
      BigStepE π p.body ⟨σAO, fac, false⟩ σ_final bodyEvents →
      Calls.CallExit fac σ p callArgs σ_final σ' →
      ----
      EvalCmdExtE π fac σ (.call n callArgs md) σ'
        (Calls.defaultAssertEvents fac σAO p.spec.preconditions ++
          bodyEvents ++
          Calls.defaultAssertEvents fac σ_final p.spec.postconditions)

end

/-! ## Contract-based command semantics -/

/-- Event-producing contract abstraction of `CmdExt P`: a call is replaced by its
    specification instead of running its body.  Base commands delegate to
    `EvalCmdE`.  A call emits its non-free preconditions as assertions at the callee
    entry frame, havocs the output formals, emits every postcondition as an
    assumption at the post-havoc frame, and writes the outputs back to the caller.
    No procedure body is executed. -/
inductive EvalCmdExtContractE [HasVal P]
    (π : String → Option (Procedure P (CmdExt P) Hdr)) :
    P.Factory → SemanticStore P → CmdExt P → SemanticStore P → Trace P → Prop where
  | cmd_sem {fac σ c σ' emitted} :
      EvalCmdE (P := P) fac σ c σ' emitted →
      ----
      EvalCmdExtContractE π fac σ (.cmd c) σ' emitted

  /-- Arguments are matched positionally as in `EvalCmdExtE.call_sem`. -/
  -- TODO: Instantiate procedure type variables for polymorphic calls.
  | call_sem {σ σO n p callArgs σ' md fac σAO} :
      π n = .some p →
      Calls.CallEntry fac σ p callArgs σAO →
      Calls.HavocVars fac σAO (ProcedureHeader.outputParams (P := P) p.header) σO →
      Calls.CallExit fac σ p callArgs σO σ' →
      ----
      EvalCmdExtContractE π fac σ (.call n callArgs md) σ'
        (Calls.defaultAssertEvents fac σAO p.spec.preconditions ++
          Calls.assumeEvents fac σO p.spec.postconditions)

/-- Reflexive-transitive statement execution over the call-aware command relation,
    with chronological events. -/
abbrev StepStmtExtStarE
    (π : String → Option (Procedure P (CmdExt P) Hdr)) :=
  ReflTransTrace (StepStmtE P (EvalCmdExtE π))

/-- One statement step over the call-aware command relation. -/
abbrev StepStmtExtE
    (π : String → Option (Procedure P (CmdExt P) Hdr)) :=
  StepStmtE P (EvalCmdExtE π)

end

end Imperative
