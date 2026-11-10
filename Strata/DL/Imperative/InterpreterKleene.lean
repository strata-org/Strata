/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Interpreter
public import Strata.DL.Imperative.InterpreterCFG
public import Strata.DL.Imperative.KleeneStmt
public import Strata.DL.Imperative.KleeneStmtSemantics

/-! # The monadic Kleene interpreter

The executable, monad-generic companion to the relational `StepKleeneE`
(`KleeneStmtSemantics.lean`), the sibling of the structured `runInterp`.  It
reuses the shared, IR-independent command/effect core — the caller supplies a
monadic command stepper (for Core: a call-aware store-stepper built on
`stepBaseCmdStore` / `Calls.stepCmd`), which executes one `CmdT`, emits its
events via `InterpEffects.emit`, and draws nondeterminism via
`InterpEffects.choose` — so this module supplies only the *control-flow* driver.
Because it is generic in `m [InterpEffects P m]`, the `ReplayM` and `EvalM`
instances both run Kleene programs unchanged.

Correspondence to `StepKleeneE`:
* `.stmt (.cmd c) ρ`      ↔ `StepKleeneE.step_cmd` (one command via `stepCmd`).
* `.stmt (.seq s1 s2) ρ`  ↔ `StepKleeneE.step_seq`.
* `.stmt (.choice s1 s2) ρ` ↔ `StepKleeneE.step_choice_left`/`step_choice_right`:
  the nondeterministic branch is resolved by drawing a boolean via
  `InterpEffects.choose … (HasBool.boolTy)` — `tt` picks the left arm, else the
  right.
* `.stmt (.loop s) ρ`     ↔ `StepKleeneE.step_loop_zero`/`step_loop_step`: a
  drawn boolean decides continue-vs-stop; `continue` → one body iteration in its
  own block scope, sequenced with the residual loop; `stop` → terminal.  `fuel`
  bounds the total iterations.
* `.stmt (.block s) ρ`    ↔ `StepKleeneE.step_block`.
* `.seq inner s2`         ↔ `step_seq_inner` / `step_seq_done`.
* `.block frame inner`    ↔ `step_block_body` / `step_block_done`.

The monadic Kleene interpreter steps over its own configuration type `IKleeneConfig`, which mirrors
`KleeneConfig` with a scope frame (`ScopeFrame`) at each block, exactly as `IConfig` mirrors
`Config`: a block the monadic interpreter opens drops the names it defined on exit.
`IKleeneConfig.abs F` is the `KleeneConfig` a configuration stands for under the factory `F`,
`IKleeneConfig.Denoting F` says its stores denote, and `IKleeneConfig.Tracked` says every frame is
exact; a block's
frame is updated with `ScopeFrame.record` at the block's level command. Lemmas about these are in
`InterpreterKleeneProps.lean`.

As with the structured engine, a failing assert is `emit`-ted. -/

namespace Imperative

public section

/-! ## The Kleene interpreter configuration -/

/-- The monadic Kleene interpreter's configuration: `KleeneConfig` with a scope frame at each
    block. -/
inductive IKleeneConfig (P : PureExpr) [InterpLang P] (CmdT : Type) : Type where
  /-- A single statement to execute next. -/
  | stmt : KleeneStmt P CmdT → IEnv P → IKleeneConfig P CmdT
  /-- A sequence context: the inner configuration, then the right statement. -/
  | seq : IKleeneConfig P CmdT → KleeneStmt P CmdT → IKleeneConfig P CmdT
  /-- Execution has finished. -/
  | terminal : IEnv P → IKleeneConfig P CmdT
  /-- A block context with its scope frame. -/
  | block : ScopeFrame P → IKleeneConfig P CmdT → IKleeneConfig P CmdT

section Config

variable {P : PureExpr} [InterpLang P] {CmdT : Type}

/-- The `KleeneConfig` a Kleene interpreter configuration stands for: each frame becomes its
    parent store. -/
@[expose] def IKleeneConfig.abs [DecidableEq P.Ident] (F : P.Factory) :
    IKleeneConfig P CmdT → KleeneConfig P CmdT
  | .stmt s ρ => .stmt s (ρ.abs F)
  | .seq inner s => .seq (inner.abs F) s
  | .terminal ρ => .terminal (ρ.abs F)
  | .block fr inner => .block (InterpLang.absStore F fr.parent.get) (inner.abs F)

/-- Every runtime store of the Kleene configuration denotes under `F`, and every environment
    carries the runtime factory of `F`. -/
@[expose] def IKleeneConfig.Denoting [DecidableEq P.Ident] (F : P.Factory) :
    IKleeneConfig P CmdT → Prop
  | .stmt _ ρ | .terminal ρ => RStore.Denoting F ρ.store.get ∧ ρ.factory = InterpLang.rfactory F
  | .seq inner _ => inner.Denoting F
  | .block fr inner => RStore.Denoting F fr.parent.get ∧ inner.Denoting F

/-- The environment of the configuration's leaf. -/
@[expose] def IKleeneConfig.getEnv : IKleeneConfig P CmdT → IEnv P
  | .stmt _ ρ | .terminal ρ => ρ
  | .seq inner _ | .block _ inner => inner.getEnv

/-- The store of the configuration's level: the parent store of the topmost block below a `.seq`
    spine, or the leaf store when there is none. -/
@[expose] def IKleeneConfig.lvl [DecidableEq P.Ident] : IKleeneConfig P CmdT → RStore P
  | .seq inner _ => inner.lvl
  | .block fr _ => fr.parent.get
  | .stmt _ ρ | .terminal ρ => ρ.store.get

/-- The command the next step runs at the configuration's level. -/
@[expose] def IKleeneConfig.levelCmd? : IKleeneConfig P CmdT → Option CmdT
  | .stmt (.cmd c) _ => some c
  | .seq inner _ => inner.levelCmd?
  | _ => none

/-- The `KleeneConfig` counterpart of `IKleeneConfig.lvl`. -/
@[expose] def KleeneConfig.lvl : KleeneConfig P CmdT → SemanticStore P
  | .seq inner _ => inner.lvl
  | .block σ _ => σ
  | .stmt _ ρ | .terminal ρ => ρ.store

/-- The `KleeneConfig` counterpart of `IKleeneConfig.levelCmd?`. -/
@[expose] def KleeneConfig.levelCmd? : KleeneConfig P CmdT → Option CmdT
  | .stmt (.cmd c) _ => some c
  | .seq inner _ => inner.levelCmd?
  | _ => none

/-- Every frame on the configuration's spine is exact for its inner level store. -/
@[expose] def IKleeneConfig.Tracked [DecidableEq P.Ident] : IKleeneConfig P CmdT → Prop
  | .seq inner _ => inner.Tracked
  | .block fr inner => fr.Exact inner.lvl ∧ inner.Tracked
  | _ => True

end Config

variable {P : PureExpr} {CmdT : Type} {m : Type → Type}
variable [HasBool P] [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P] [CmdDefs P CmdT]
    [Monad m] [InterpEffects P m] [MonadExcept StopReason m]

/-- One Kleene step, mirroring `StepKleeneE`.  `stepCmd` is the shared monadic
    command stepper; `fuel` is the bounded-eval budget threaded to it.  A `.choice` or `.loop`
    draws its branch as a nondeterministic guard (`resolveGuard` on `.nondet`): a Boolean value
    of `choose`, read up to metadata (`InterpLang.boolLit?`), any other value being an error
    (`expectedBooleanChoice`). -/
def stepInterpKleene
    (stepCmd : StepCmdStoreM P CmdT m) (fuel : Nat) :
    IKleeneConfig P CmdT → m (IKleeneConfig P CmdT)
  | .stmt (.choice s1 s2) ρ => do
    let b ← resolveGuard fuel ρ .nondet
    pure (.stmt (if b then s1 else s2) ρ)
  | .stmt (.loop s) ρ => do
    let b ← resolveGuard fuel ρ .nondet
    if b then
      pure (.seq (.block (.opened ρ.store) (.stmt s ρ)) (.loop s))
    else
      pure (.terminal ρ)
  | .stmt (.cmd c) ρ => do
    let σ' ← stepCmd fuel ρ.factory ρ.store c
    pure (.terminal { ρ with store := σ' })
  | .stmt (.seq s1 s2) ρ => pure (.seq (.stmt s1 ρ) s2)
  | .stmt (.block s) ρ => pure (.block (.opened ρ.store) (.stmt s ρ))
  | .seq inner s2 => do
    match inner with
    | .terminal ρ' => pure (.stmt s2 ρ')
    | _ =>
      let inner' ← stepInterpKleene stepCmd fuel inner
      pure (.seq inner' s2)
  | .block frame inner => do
    match inner with
    | .terminal ρ' => pure (.terminal { ρ' with store := frame.exit ρ'.store })
    | _ =>
      let inner' ← stepInterpKleene stepCmd fuel inner
      pure (.block (frame.record inner.levelCmd?) inner')
  | .terminal ρ => pure (.terminal ρ)

/-- The Kleene driver: step until a `.terminal` config or fuel runs out.  Mirrors
    `runInterp` (structural fuel recursion); `0` fuel on a non-terminal config
    throws `replayFuelExhausted`. -/
def runInterpKleene
    (stepCmd : StepCmdStoreM P CmdT m) :
    Nat → IKleeneConfig P CmdT → m (IKleeneConfig P CmdT)
  | fuel, cfgc =>
    match cfgc with
    | .terminal _ => pure cfgc
    | _ =>
      match fuel with
      | 0 => throw .replayFuelExhausted
      | fuel + 1 => do
        let next ← stepInterpKleene stepCmd (fuel + 1) cfgc
        runInterpKleene stepCmd fuel next

end -- public section

end Imperative
