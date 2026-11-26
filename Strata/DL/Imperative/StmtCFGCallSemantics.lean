/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CFGSemantics
public import Strata.DL.Imperative.CmdCallFormals
public import Strata.DL.Imperative.StmtSemantics

/-! # Reference semantics of procedure calls, over any `PureExpr`

This file gives the event-producing meaning of procedure calls for any expression language
`P` and any command type `CmdT`. A command semantics `Calls.CmdSem` tells, per command, whether
it is a base command, a call, or an extension command, which `Calls.CmdSem.ExtE` relates to the
store it ends in or to a call it resolves to. `EvalCmdViewE` (one command) and `BigStepViewE`
(one procedure body) are the call-aware semantics over a command semantics. The semantics of
`CmdExt P`, a base command or a procedure call, is the one at `Calls.CmdExt.sem`:
`EvalCmdExtE` and `BigStepE`, with the rules `EvalCmdExtE.cmd_sem`, `EvalCmdExtE.call_sem`,
`EvalCmdExtE.call_abstract_sem`, `BigStepE.structured` and `BigStepE.cfg`, and the case analyses
`EvalCmdExtE.casesOn'` and `BigStepE.casesOn'`.

A call `call n<tyArgs> args` runs the procedure `π n` instantiated at the call's type
arguments (`Calls.typeInstantiatedCallee`, through the dialect's `ProcedureTypeInstantiation`),
written `p` below, to completion in one command step:
- *Entry* (`Calls.CallEntry`): evaluate the input and inout arguments in the
  caller's store, read the caller's `out` variables, and build a fresh callee
  frame binding the input formals and the output-only formals.  Every inout
  formal `g` is also bound under `HasOldIdent.mkOld g` to its entry value (its
  *old snapshot*), so that postconditions can refer to it.
- *Precondition events*: each non-free precondition is emitted as an assertion
  event, evaluated in the entry frame, with its *site metadata*: the clause's
  metadata with the call statement's provenance as primary provenance
  (`Calls.checksAtCall`), so that the checks of two calls at different source
  positions are different assertions.
- *Body*: the body runs from the entry frame until it terminates, emitting its own
  events.  An opaque callee (`Body.isOpaque`: an abstract body, or a body marked opaque) is
  not run: its call havocs the output formals instead and emits every postcondition as an
  assumption event, as `EvalCmdExtContractE` does (`EvalCmdExtE.call_abstract_sem`).
- *Postcondition events*: each non-free postcondition is emitted as an assertion
  event, evaluated in the callee's final frame.
- *Exit* (`Calls.CallExit`): read the output formals in the final frame and write
  them back to the caller's `out`/`inout` variables.
The call's trace is the precondition events, then the body events, then the
postcondition events; for an opaque callee it is the precondition events, then the
postcondition assumption events.

`EvalCmdViewE` (one command) and `BigStepViewE` (one procedure body) are mutually
inductive: a call's derivation contains a `BigStepViewE` derivation of the callee body. A
structured body is a multi-step run of `StepStmtE`; a CFG body is a multi-step run of
`StepCFGE`. Both relations obtain
their execution environment from their configurations, and both evaluate commands
with `EvalCmdViewE` itself. Nested calls therefore nest derivations.

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

/-- The procedure a call to `n` with type arguments `tyArgs` runs: `π`'s procedure `n`,
    instantiated at `tyArgs`.  A call without type arguments (`none`) instantiates at `[]`,
    so it runs a monomorphic callee as it is and has no callee if `n` is polymorphic.  The type
    checker records type arguments on every call to a polymorphic procedure, so such a call
    arises only in a program that was not type-checked; there it has no step, and a theorem
    about the program says nothing about what follows the call. -/
@[expose] def typeInstantiatedCallee [ProcedureTypeInstantiation P Hdr]
    (π : String → Option (Procedure P (CmdExt P) Hdr)) (n : String)
    (tyArgs : Option (List P.Ty)) : Option (Procedure P (CmdExt P) Hdr) :=
  (π n).bind (ProcedureTypeInstantiation.instantiate · (tyArgs.getD []))

/-- Initialize a callee-local frame without colliding with caller names: starting
    from the empty store, the input formals are bound to `inputVals`, the
    output-only formals to `outOnlyVals`, and every inout formal is snapshotted
    under its `old` name. -/
@[expose] def InitCallFrame
    {C : Type} (p : Procedure P C Hdr) (inputVals : List P.Val) (outOnlyVals : List P.Val)
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

/-- The specification clauses `checks` as checked at a call whose statement has metadata
    `callMd`: each clause's metadata takes the call site as its primary provenance
    (`MetaData.setCallSiteFileRange`), the metadata call elimination gives the assertion it
    generates for the clause, so that the checks of two calls at different source positions
    are different assertions. -/
@[expose] def checksAtCall (callMd : MetaData P)
    (checks : ListMap String (Check P)) : ListMap String (Check P) :=
  checks.toList.map fun (label, check) =>
    (label, { check with md := check.md.setCallSiteFileRange callMd })

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
    {C : Type} (p : Procedure P C Hdr) (callArgs : List (CallArg P)) (σAO : SemanticStore P) :
    Prop :=
  ∃ inputVals outOnlyVals,
    EvalExpressions fac σ (getInputExprs callArgs) inputVals ∧
    ReadValues fac σ (CallArg.getOutArgs callArgs) outOnlyVals ∧
    InitCallFrame p inputVals outOnlyVals σAO

/-- Shared epilogue of the call rule: read the callee's output formals in its final
    store and write them back positionally to the caller's `out`/`inout` variables,
    which must be distinct.  Each value written back must have the type of the value the
    caller variable held (`HasVal.valueOfStoredTy`), as for `set`.  This restricts the
    semantics: a call whose output value has another type than the caller variable has no
    exit, so its runs stop at the call.  It keeps the caller's variables at their types
    across the call. -/
@[expose] def CallExit (fac : P.Factory) (σ : SemanticStore P)
    {C : Type} (p : Procedure P C Hdr) (callArgs : List (CallArg P))
    (σEnd σ' : SemanticStore P) : Prop :=
  (CallArg.getLhs callArgs).Nodup ∧
  ∃ outputVals,
    ReadValues fac σEnd (ProcedureHeader.outputParams (P := P) p.header) outputVals ∧
    UpdateStates σ (CallArg.getLhs callArgs) outputVals σ' ∧
    List.Rel₂ (HasVal.valueOfStoredTy (P := P) fac σ) (CallArg.getLhs callArgs) outputVals

end Entry

end Calls

/-! ## Call-aware command semantics -/

namespace Calls

/-- What a command is, to the call-aware semantics: a base command, a call of
    `procName` with its arguments, its metadata and the instantiation `inst` of the callee it
    runs (at the call's type arguments), or an extension command, related by `CmdSem.ExtE`. -/
inductive CmdKind (P : PureExpr) (CmdT : Type) (Hdr : Type) [DecidableEq Hdr] [Inhabited Hdr]
    where
  /-- A base command, evaluated by `EvalCmdE`. -/
  | base (c : Cmd P)
  /-- A call of `procName` with its arguments and metadata, whose callee is instantiated by
      `inst`. -/
  | call (procName : String) (args : List (CallArg P)) (md : MetaData P)
      (inst : Procedure P CmdT Hdr → Option (Procedure P CmdT Hdr))
  /-- An extension command, related to its outcome by `CmdSem.ExtE`. -/
  | ext

/-- What an extension command ends in: a store, or a call of `procName` that it resolves to
    from the store `σ'` it reached, with the call's arguments, metadata and callee instantiation. -/
inductive ExtOutcome (P : PureExpr) (CmdT : Type) (Hdr : Type) [DecidableEq Hdr] [Inhabited Hdr]
    where
  /-- The extension command ends in the store `σ'`. -/
  | done (σ' : SemanticStore P)
  /-- The extension command resolves to a call of `procName`, run from the store `σ'` it reached,
      which the call's outputs are written back into. -/
  | call (σ' : SemanticStore P) (procName : String) (args : List (CallArg P)) (md : MetaData P)
      (inst : Procedure P CmdT Hdr → Option (Procedure P CmdT Hdr))

/-- A command semantics for the command type `CmdT`: what each command is (`kind`), and the
    relation `ExtE fac σ c o evs` of an extension command `c`, run at the factory `fac` from
    the store `σ`, to its outcome `o` with the events `evs`. -/
structure CmdSem (P : PureExpr) (CmdT : Type) (Hdr : Type) [DecidableEq Hdr] [Inhabited Hdr] where
  kind : CmdT → CmdKind P CmdT Hdr
  ExtE : P.Factory → SemanticStore P → CmdT → ExtOutcome P CmdT Hdr → Trace P → Prop

section CmdExtSem

variable {P : PureExpr} {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr]
  [ProcedureTypeInstantiation P Hdr]

/-- The command semantics of `CmdExt P`: a `.cmd` is a base command, a `.call` is a call whose
    callee is instantiated at its type arguments (`ProcedureTypeInstantiation.instantiate`), and
    there is no extension command. -/
@[expose] def CmdExt.sem : CmdSem P (CmdExt P) Hdr where
  kind
    | .cmd c => .base c
    | .call procName tyArgs args md =>
      .call procName args md fun p => ProcedureTypeInstantiation.instantiate p (tyArgs.getD [])
  ExtE _ _ _ _ _ := False


/-- A `CmdExt` command that `CmdExt.sem` takes for the base command `b` is `.cmd b`. -/
theorem CmdExt.sem_kind_base {c : CmdExt P} {b : Cmd P}
    (h : (CmdExt.sem (Hdr := Hdr)).kind c = .base b) : c = .cmd b := by
  cases c <;> simp_all [CmdExt.sem]

/-- A `CmdExt` command that `CmdExt.sem` takes for a call is that call, with the instantiation
    at its type arguments. -/
theorem CmdExt.sem_kind_call {c : CmdExt P} {n : String} {args : List (CallArg P)}
    {md : MetaData P} {inst : Procedure P (CmdExt P) Hdr → Option (Procedure P (CmdExt P) Hdr)}
    (h : (CmdExt.sem (Hdr := Hdr)).kind c = .call n args md inst) :
    ∃ tyArgs, c = .call n tyArgs args md ∧
      inst = fun p => ProcedureTypeInstantiation.instantiate p (tyArgs.getD []) := by
  cases c with
  | cmd => simp [CmdExt.sem] at h
  | call n' tyArgs args' md' =>
    simp only [CmdExt.sem, CmdKind.call.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨tyArgs, rfl, rfl⟩

/-- A command that `CmdExt.sem` takes for a call of `n` whose callee `π n` instantiates to `p` is
    a call of `n` at type arguments for which `p` is the instantiated callee. -/
theorem CmdExt.sem_kind_call_callee {π : String → Option (Procedure P (CmdExt P) Hdr)}
    {c : CmdExt P} {n : String} {args : List (CallArg P)} {md : MetaData P}
    {inst : Procedure P (CmdExt P) Hdr → Option (Procedure P (CmdExt P) Hdr)}
    {p₀ p : Procedure P (CmdExt P) Hdr}
    (hk : (CmdExt.sem (Hdr := Hdr)).kind c = .call n args md inst)
    (h₀ : π n = some p₀) (h : inst p₀ = some p) :
    ∃ tyArgs, c = .call n tyArgs args md ∧ typeInstantiatedCallee π n tyArgs = some p := by
  obtain ⟨tyArgs, rfl, rfl⟩ := CmdExt.sem_kind_call hk
  exact ⟨tyArgs, rfl, by simp [typeInstantiatedCallee, h₀, h]⟩

/-- No `CmdExt` command is an extension command under `CmdExt.sem`. -/
theorem CmdExt.sem_kind_ne_ext (c : CmdExt P) : (CmdExt.sem (Hdr := Hdr)).kind c ≠ .ext := by
  cases c <;> simp [CmdExt.sem]

end CmdExtSem

end Calls

section ViewSemantics

variable {P : PureExpr}
  [DecidableEq P.Ident] [HasOldIdent P]
  {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]
  [HasBool P] [HasBoolOps P] [HasFvar P] [HasFvars P] {CmdT : Type}

mutual

/-- Event-producing execution of a procedure body, structured or CFG, over `EvalCmdViewE S π`,
    as `BigStepE` is over `EvalCmdExtE π`: a structured body runs as `.block "" ss` to a
    terminal configuration, a CFG body from its entry block to `finish`, and its final store is
    projected through the entry store. -/
inductive BigStepViewE (S : Calls.CmdSem P CmdT Hdr)
    (π : String → Option (Procedure P CmdT Hdr)) :
    Body P CmdT → Env P → SemanticStore P → Trace P → Prop where
  | structured :
      ReflTransTrace (StepStmtE P (EvalCmdViewE S π))
        (.stmt (Stmt.block "" ss #[]) ρ)
        emitted
        (.terminal ρ') →
      ----
      BigStepViewE S π (.structured ss opq) ρ ρ'.store emitted
  | cfg :
      ReflTransTrace (StepCFGE P (EvalCmdViewE S π))
        (.atBlock g g.entry ρ)
        emitted
        (.terminal ρ') →
      ----
      BigStepViewE S π (.cfg g opq) ρ (projectStore ρ.store ρ'.store) emitted

/-- Event-producing semantics of the commands of `CmdT` under the command semantics `S` and the
    callee table `π`, as `EvalCmdExtE` is for `CmdExt P`. A base command delegates to `EvalCmdE`,
    a call runs as in `EvalCmdExtE.call_sem`, or as its contract when its callee is opaque
    (`EvalCmdExtE.call_abstract_sem`), and an extension command follows `S.ExtE`. -/
inductive EvalCmdViewE (S : Calls.CmdSem P CmdT Hdr)
    (π : String → Option (Procedure P CmdT Hdr)) :
    P.Factory → SemanticStore P → CmdT → SemanticStore P → Trace P → Prop where
  /-- A base command `b` evaluates as `EvalCmdE` evaluates `b`. -/
  | base_sem {fac σ c b σ' emitted} :
      S.kind c = .base b →
      EvalCmdE (P := P) fac σ b σ' emitted →
      ----
      EvalCmdViewE S π fac σ c σ' emitted
  /-- A call of `n` runs the callee `p₀` of `π`, instantiated by `inst` to a `p` that is not
      opaque: entry frame, precondition events with the call's site metadata, body,
      postcondition events, write-back. -/
  | call_sem {σ c n inst p₀ p callArgs σ' σ_final bodyEvents md fac σAO} :
      S.kind c = .call n callArgs md inst →
      π n = .some p₀ →
      inst p₀ = .some p →
      p.body.isOpaque = false →
      Calls.CallEntry fac σ p callArgs σAO →
      BigStepViewE S π p.body ⟨σAO, fac⟩ σ_final bodyEvents →
      Calls.CallExit fac σ p callArgs σ_final σ' →
      ----
      EvalCmdViewE S π fac σ c σ'
        (Calls.defaultAssertEvents fac σAO (Calls.checksAtCall md p.spec.preconditions) ++
          bodyEvents ++
          Calls.defaultAssertEvents fac σ_final p.spec.postconditions)
  /-- A call of `n` whose callee `p₀` of `π`, instantiated by `inst` to `p`, is opaque runs as its
      contract: entry frame, precondition events with the call's site metadata, havoc of the
      output formals, every postcondition as an assumption at the post-havoc frame, write-back. -/
  | call_contract_sem {σ σO c n inst p₀ p callArgs σ' md fac σAO} :
      S.kind c = .call n callArgs md inst →
      π n = .some p₀ →
      inst p₀ = .some p →
      p.body.isOpaque = true →
      Calls.CallEntry fac σ p callArgs σAO →
      Calls.HavocVars fac σAO (ProcedureHeader.outputParams (P := P) p.header) σO →
      Calls.CallExit fac σ p callArgs σO σ' →
      ----
      EvalCmdViewE S π fac σ c σ'
        (Calls.defaultAssertEvents fac σAO (Calls.checksAtCall md p.spec.preconditions) ++
          Calls.assumeEvents fac σO p.spec.postconditions)
  /-- An extension command that ends in the store `σ'` steps to `σ'` with its own events. -/
  | ext_sem {fac σ c σ' emitted} :
      S.kind c = .ext →
      S.ExtE fac σ c (.done σ') emitted →
      ----
      EvalCmdViewE S π fac σ c σ' emitted
  /-- An extension command that resolves to a call of `n` from the store `σ₁` it reached runs that
      call as `call_sem` does, from `σ₁` and at the same factory: the callee frame is built from
      `σ₁`, and the outputs are written back into `σ₁`. Its events are its own, then the call's. -/
  | ext_call_sem {σ σ₁ c n inst p₀ p callArgs σ' σ_final extEvents bodyEvents md fac σAO} :
      S.kind c = .ext →
      S.ExtE fac σ c (.call σ₁ n callArgs md inst) extEvents →
      π n = .some p₀ →
      inst p₀ = .some p →
      p.body.isOpaque = false →
      Calls.CallEntry fac σ₁ p callArgs σAO →
      BigStepViewE S π p.body ⟨σAO, fac⟩ σ_final bodyEvents →
      Calls.CallExit fac σ₁ p callArgs σ_final σ' →
      ----
      EvalCmdViewE S π fac σ c σ'
        (extEvents ++
          Calls.defaultAssertEvents fac σAO (Calls.checksAtCall md p.spec.preconditions) ++
          bodyEvents ++
          Calls.defaultAssertEvents fac σ_final p.spec.postconditions)
  /-- An extension command that resolves to a call of `n` from the store `σ₁` it reached, whose
      callee is opaque, runs that call as its contract, as `call_contract_sem` does, from `σ₁`. Its
      events are its own, then the call's. -/
  | ext_call_contract_sem {σ σ₁ σO c n inst p₀ p callArgs σ' extEvents md fac σAO} :
      S.kind c = .ext →
      S.ExtE fac σ c (.call σ₁ n callArgs md inst) extEvents →
      π n = .some p₀ →
      inst p₀ = .some p →
      p.body.isOpaque = true →
      Calls.CallEntry fac σ₁ p callArgs σAO →
      Calls.HavocVars fac σAO (ProcedureHeader.outputParams (P := P) p.header) σO →
      Calls.CallExit fac σ₁ p callArgs σO σ' →
      ----
      EvalCmdViewE S π fac σ c σ'
        (extEvents ++
          Calls.defaultAssertEvents fac σAO (Calls.checksAtCall md p.spec.preconditions) ++
          Calls.assumeEvents fac σO p.spec.postconditions)

end

end ViewSemantics

variable {P : PureExpr}
  [DecidableEq P.Ident] [HasOldIdent P]
  {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]
  [ProcedureTypeInstantiation P Hdr]
  [HasBool P] [HasBoolOps P] [HasFvar P] [HasFvars P]

/-- Event-producing execution of a procedure body of `CmdExt P`, structured or CFG, from its
    entry environment to normal termination: `BigStepViewE` at `Calls.CmdExt.sem`.  Inner
    scoping does not leak past the call: variables initialized by the body are dropped from the
    final store. -/
@[expose] def BigStepE (π : String → Option (Procedure P (CmdExt P) Hdr)) :
    Body P (CmdExt P) → Env P → SemanticStore P → Trace P → Prop :=
  BigStepViewE (Calls.CmdExt.sem (Hdr := Hdr)) π

/-- Event-producing command semantics of `CmdExt P`: `EvalCmdViewE` at `Calls.CmdExt.sem`.
    Base commands delegate to `EvalCmdE`.  A call emits its non-free preconditions as
    assertions at the callee entry frame, each with its site metadata at the call
    (`Calls.checksAtCall md`), executes its body from that frame, and emits its non-free
    postconditions, with their own metadata, as assertions at the callee's final frame. The
    call runs its body and interprets each contract clause with the active factory `fac`. A call
    to an opaque procedure uses its contract instead (`call_abstract_sem`). -/
@[expose] def EvalCmdExtE (π : String → Option (Procedure P (CmdExt P) Hdr)) :
    P.Factory → SemanticStore P → CmdExt P → SemanticStore P → Trace P → Prop :=
  EvalCmdViewE (Calls.CmdExt.sem (Hdr := Hdr)) π

/-- A structured body runs wrapped in `Stmt.block "" ss #[]`, which scopes `init`s and catches
    `exit ""`. -/
theorem BigStepE.structured {π : String → Option (Procedure P (CmdExt P) Hdr)}
    {ss : List (Stmt P (CmdExt P))} {opq : Bool} {ρ ρ' : Env P} {emitted : Trace P}
    (h : ReflTransTrace (StepStmtE P (EvalCmdExtE π)) (.stmt (Stmt.block "" ss #[]) ρ) emitted
      (.terminal ρ')) :
    BigStepE π (.structured ss opq) ρ ρ'.store emitted :=
  BigStepViewE.structured h

/-- A CFG body runs from its entry block to `finish`; the final store is projected through the
    entry store to drop body-local variables. -/
theorem BigStepE.cfg {π : String → Option (Procedure P (CmdExt P) Hdr)}
    {g : DetCFG P (CmdExt P)} {opq : Bool} {ρ ρ' : Env P} {emitted : Trace P}
    (h : ReflTransTrace (StepCFGE P (EvalCmdExtE π)) (.atBlock g g.entry ρ) emitted
      (.terminal ρ')) :
    BigStepE π (.cfg g opq) ρ (projectStore ρ.store ρ'.store) emitted :=
  BigStepViewE.cfg h

/-- A base command evaluates as `EvalCmdE` evaluates it. -/
theorem EvalCmdExtE.cmd_sem {π : String → Option (Procedure P (CmdExt P) Hdr)}
    {fac : P.Factory} {σ σ' : SemanticStore P} {c : Cmd P} {emitted : Trace P}
    (h : EvalCmdE (P := P) fac σ c σ' emitted) :
    EvalCmdExtE π fac σ (.cmd c) σ' emitted :=
  EvalCmdViewE.base_sem rfl h

/-- Arguments are matched positionally in three alignments:
    `Calls.getInputExprs callArgs` ↔ `ProcedureHeader.inputParams p.header`;
    `CallArg.getLhs callArgs` ↔ `ProcedureHeader.outputParams p.header`; and
    `CallArg.getOutArgs callArgs` ↔ `Calls.outputOnlyParams p.header`.  The third alignment
    follows from the second because every inout formal is passed as `.inoutArg`.  The callee `p`
    is `π`'s procedure `n` instantiated at the call's type arguments
    (`Calls.typeInstantiatedCallee`).  This rule applies to a callee whose body is not opaque; a
    call to an opaque procedure uses its contract instead (`call_abstract_sem`). -/
theorem EvalCmdExtE.call_sem {π : String → Option (Procedure P (CmdExt P) Hdr)}
    {σ : SemanticStore P} {n : String} {tyArgs : Option (List P.Ty)}
    {p : Procedure P (CmdExt P) Hdr} {callArgs : List (CallArg P)} {σ' σ_final : SemanticStore P}
    {bodyEvents : Trace P} {md : MetaData P} {fac : P.Factory} {σAO : SemanticStore P}
    (hπ : Calls.typeInstantiatedCallee π n tyArgs = .some p)
    (hno : p.body.isOpaque = false)
    (hentry : Calls.CallEntry fac σ p callArgs σAO)
    (hbody : BigStepE π p.body ⟨σAO, fac⟩ σ_final bodyEvents)
    (hexit : Calls.CallExit fac σ p callArgs σ_final σ') :
    EvalCmdExtE π fac σ (.call n tyArgs callArgs md) σ'
      (Calls.defaultAssertEvents fac σAO (Calls.checksAtCall md p.spec.preconditions) ++
        bodyEvents ++
        Calls.defaultAssertEvents fac σ_final p.spec.postconditions) := by
  obtain ⟨p₀, hp₀, hinst⟩ := Option.bind_eq_some_iff.1 hπ
  exact EvalCmdViewE.call_sem rfl hp₀ hinst hno hentry hbody hexit

/-- A call to an opaque procedure (`Body.isOpaque`) has the meaning of its contract, as in
    `EvalCmdExtContractE.call_sem`: it emits the non-free preconditions as assertions at the
    callee entry frame, havocs the output formals, emits every postcondition as an assumption at
    the post-havoc frame, and writes the outputs back to the caller.  Arguments are matched
    positionally, and the callee is instantiated at the call's type arguments, as in
    `call_sem`. -/
theorem EvalCmdExtE.call_abstract_sem {π : String → Option (Procedure P (CmdExt P) Hdr)}
    {σ σO : SemanticStore P} {n : String} {tyArgs : Option (List P.Ty)}
    {p : Procedure P (CmdExt P) Hdr} {callArgs : List (CallArg P)} {σ' : SemanticStore P}
    {md : MetaData P} {fac : P.Factory} {σAO : SemanticStore P}
    (hπ : Calls.typeInstantiatedCallee π n tyArgs = .some p)
    (ho : p.body.isOpaque = true)
    (hentry : Calls.CallEntry fac σ p callArgs σAO)
    (hhavoc : Calls.HavocVars fac σAO (ProcedureHeader.outputParams (P := P) p.header) σO)
    (hexit : Calls.CallExit fac σ p callArgs σO σ') :
    EvalCmdExtE π fac σ (.call n tyArgs callArgs md) σ'
      (Calls.defaultAssertEvents fac σAO (Calls.checksAtCall md p.spec.preconditions) ++
        Calls.assumeEvents fac σO p.spec.postconditions) := by
  obtain ⟨p₀, hp₀, hinst⟩ := Option.bind_eq_some_iff.1 hπ
  exact EvalCmdViewE.call_contract_sem rfl hp₀ hinst ho hentry hhavoc hexit

/-- Case analysis on `EvalCmdExtE` by its three rules, a base command (`cmd_sem`), a call
    (`call_sem`) and a call to an opaque callee (`call_abstract_sem`), as for an inductive with
    those constructors. -/
@[elab_as_elim, cases_eliminator]
theorem EvalCmdExtE.casesOn' {π : String → Option (Procedure P (CmdExt P) Hdr)}
    {motive : ∀ fac σ c σ' evs, EvalCmdExtE π fac σ c σ' evs → Prop}
    {fac : P.Factory} {σ : SemanticStore P} {c : CmdExt P} {σ' : SemanticStore P}
    {evs : Trace P} (h : EvalCmdExtE π fac σ c σ' evs)
    (cmd_sem : ∀ {fac σ c σ' emitted} (h : EvalCmdE (P := P) fac σ c σ' emitted),
      motive fac σ (.cmd c) σ' emitted (EvalCmdExtE.cmd_sem h))
    (call_sem : ∀ {σ n tyArgs p callArgs σ' σ_final bodyEvents md fac σAO}
      (hπ : Calls.typeInstantiatedCallee π n tyArgs = .some p)
      (hno : p.body.isOpaque = false)
      (hentry : Calls.CallEntry fac σ p callArgs σAO)
      (hbody : BigStepE π p.body ⟨σAO, fac⟩ σ_final bodyEvents)
      (hexit : Calls.CallExit fac σ p callArgs σ_final σ'),
      motive fac σ (.call n tyArgs callArgs md) σ'
        (Calls.defaultAssertEvents fac σAO (Calls.checksAtCall md p.spec.preconditions) ++
          bodyEvents ++
          Calls.defaultAssertEvents fac σ_final p.spec.postconditions)
        (EvalCmdExtE.call_sem hπ hno hentry hbody hexit))
    (call_abstract_sem : ∀ {σ σO n tyArgs p callArgs σ' md fac σAO}
      (hπ : Calls.typeInstantiatedCallee π n tyArgs = .some p)
      (ho : p.body.isOpaque = true)
      (hentry : Calls.CallEntry fac σ p callArgs σAO)
      (hhavoc : Calls.HavocVars fac σAO (ProcedureHeader.outputParams (P := P) p.header) σO)
      (hexit : Calls.CallExit fac σ p callArgs σO σ'),
      motive fac σ (.call n tyArgs callArgs md) σ'
        (Calls.defaultAssertEvents fac σAO (Calls.checksAtCall md p.spec.preconditions) ++
          Calls.assumeEvents fac σO p.spec.postconditions)
        (EvalCmdExtE.call_abstract_sem hπ ho hentry hhavoc hexit)) :
    motive fac σ c σ' evs h := by
  cases h with
  | base_sem hk hb =>
    cases Calls.CmdExt.sem_kind_base hk
    exact cmd_sem hb
  | call_sem hk hπ hinst hno hentry hbody hexit =>
    obtain ⟨tyArgs, rfl, hcallee⟩ := Calls.CmdExt.sem_kind_call_callee hk hπ hinst
    exact call_sem hcallee hno hentry hbody hexit
  | call_contract_sem hk hπ hinst ho hentry hhavoc hexit =>
    obtain ⟨tyArgs, rfl, hcallee⟩ := Calls.CmdExt.sem_kind_call_callee hk hπ hinst
    exact call_abstract_sem hcallee ho hentry hhavoc hexit
  | ext_sem hk => exact absurd hk (Calls.CmdExt.sem_kind_ne_ext _)
  | ext_call_sem hk => exact absurd hk (Calls.CmdExt.sem_kind_ne_ext _)
  | ext_call_contract_sem hk => exact absurd hk (Calls.CmdExt.sem_kind_ne_ext _)

/-- Case analysis on `BigStepE` by its two rules, a structured body and a CFG body. -/
@[elab_as_elim, cases_eliminator]
theorem BigStepE.casesOn' {π : String → Option (Procedure P (CmdExt P) Hdr)}
    {motive : ∀ b ρ σ' evs, BigStepE π b ρ σ' evs → Prop}
    {b : Body P (CmdExt P)} {ρ : Env P} {σ' : SemanticStore P} {evs : Trace P}
    (h : BigStepE π b ρ σ' evs)
    (structured : ∀ {ss opq ρ ρ' emitted}
      (h : ReflTransTrace (StepStmtE P (EvalCmdExtE π)) (.stmt (Stmt.block "" ss #[]) ρ) emitted
        (.terminal ρ')),
      motive (.structured ss opq) ρ ρ'.store emitted (BigStepE.structured h))
    (cfg : ∀ {g opq ρ ρ' emitted}
      (h : ReflTransTrace (StepCFGE P (EvalCmdExtE π)) (.atBlock g g.entry ρ) emitted
        (.terminal ρ')),
      motive (.cfg g opq) ρ (projectStore ρ.store ρ'.store) emitted (BigStepE.cfg h)) :
    motive b ρ σ' evs h := by
  cases h with
  | structured R => exact structured R
  | cfg R => exact cfg R

/-! ## Contract-based command semantics -/

/-- Event-producing contract abstraction of `CmdExt P`: a call is replaced by its
    specification instead of running its body.  Base commands delegate to
    `EvalCmdE`.  A call emits its non-free preconditions as assertions at the callee
    entry frame, each with its site metadata at the call (`Calls.checksAtCall md`),
    havocs the output formals, emits every postcondition as an assumption at the
    post-havoc frame, and writes the outputs back to the caller.
    No procedure body is executed. -/
inductive EvalCmdExtContractE [HasVal P]
    (π : String → Option (Procedure P (CmdExt P) Hdr)) :
    P.Factory → SemanticStore P → CmdExt P → SemanticStore P → Trace P → Prop where
  | cmd_sem {fac σ c σ' emitted} :
      EvalCmdE (P := P) fac σ c σ' emitted →
      ----
      EvalCmdExtContractE π fac σ (.cmd c) σ' emitted

  /-- Arguments are matched positionally, and the callee instantiated, as in
      `EvalCmdExtE.call_sem`. -/
  | call_sem {σ σO n tyArgs p callArgs σ' md fac σAO} :
      Calls.typeInstantiatedCallee π n tyArgs = .some p →
      Calls.CallEntry fac σ p callArgs σAO →
      Calls.HavocVars fac σAO (ProcedureHeader.outputParams (P := P) p.header) σO →
      Calls.CallExit fac σ p callArgs σO σ' →
      ----
      EvalCmdExtContractE π fac σ (.call n tyArgs callArgs md) σ'
        (Calls.defaultAssertEvents fac σAO (Calls.checksAtCall md p.spec.preconditions) ++
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
