/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Interpreter
public import Strata.DL.Imperative.CFGSemantics
public import Strata.DL.Imperative.BasicBlock

/-! # The monadic CFG interpreter

The executable, monad-generic companion to the relational `StepCFGE`
(`CFGSemantics.lean`).  It reuses the shared, IR-independent command/effect core
— the caller supplies a monadic command stepper (for Core: `stepBaseCmdStore`,
which executes one `Cmd P`, emits its events via `InterpEffects.emit`, and draws
nondeterminism via `InterpEffects.choose`) — so this module supplies only the
*control-flow* driver.  Because it is generic in `m [InterpEffects P m]`, the
`ReplayM` and `EvalM` instances both run CFG programs unchanged.

Correspondence to `StepCFGE` (`CFGSemantics.lean`):
* `.atBlock` fetch  ↔ `StepCFGE.fetch` (`List.lookup t cfg.blocks`).
* `.inBlock (c::cs)` ↔ `StepCFGE.step_cmd` (one command via `stepCmd`).
* `.inBlock []` transfer ↔ `StepCFGE.goto_true`/`goto_false`/`finish`.

As in the structured monad-generic engine (`runInterp`), condition evaluation is
bounded: `StepCFGE` evaluates a `condGoto` guard with the unbounded `P.eval`; here the
guard is evaluated with `InterpLang.boundedEval fuel`, the same bounded evaluator
`stepBaseCmdStore` uses, so production never invokes `evalFully`. A failing assert is
`emit`-ted (the halt/collect policy lives in each instance's `emit`).

Fuel bounds the total number of steps (hence back-edges/loops): each step
consumes one unit, and `0` fuel on a non-terminal config throws
`replayFuelExhausted`, exactly as the structured `runInterp` does. -/

namespace Imperative

public section

/-- Every command of every block that a label of the CFG `g` resolves to (`List.lookup`) passes
    the check `q`. -/
@[expose] def CFG.allCmds {l CmdT : Type} {P : PureExpr} [BEq l] (q : CmdT → Bool)
    (g : CFG l (DetBlock l CmdT P)) : Prop :=
  ∀ t b, g.blocks.lookup t = some b → b.cmds.all q = true

/-- The commands a CFG configuration can still run pass the check `q`: `CFG.allCmds q` holds of
    its CFG and, in the middle of a block, every residual command passes `q`. -/
@[expose] def CFGConfig.allCmds {l CmdT : Type} {P : PureExpr} [BEq l] (q : CmdT → Bool) :
    CFGConfig l CmdT P → Prop
  | .atBlock g _ _ => g.allCmds q
  | .inBlock g _ cs _ _ => g.allCmds q ∧ cs.all q = true
  | .terminal _ => True

variable {P : PureExpr} {l CmdT : Type} {m : Type → Type}
variable [HasBool P] [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P]
    [Monad m] [InterpEffects P m] [MonadExcept StopReason m] [BEq l]

/-- The monadic CFG interpreter's configuration: `CFGConfig` with an interpreter environment
    (`IEnv`). -/
inductive ICFGConfig (l CmdT : Type) (P : PureExpr) [InterpLang P] : Type where
  /-- About to fetch the block at a label of the CFG. -/
  | atBlock : CFG l (DetBlock l CmdT P) → l → IEnv P → ICFGConfig l CmdT P
  /-- Mid-block: residual commands and the block's transfer. -/
  | inBlock : CFG l (DetBlock l CmdT P) → l → List CmdT → DetTransferCmd l P → IEnv P →
      ICFGConfig l CmdT P
  /-- Execution has finished. -/
  | terminal : IEnv P → ICFGConfig l CmdT P

/-- The environment of a CFG interpreter configuration. -/
@[expose] def ICFGConfig.env {l CmdT : Type} {P : PureExpr} [InterpLang P] :
    ICFGConfig l CmdT P → IEnv P
  | .atBlock _ _ ρ | .inBlock _ _ _ _ ρ | .terminal ρ => ρ

/-- The `CFGConfig` a CFG interpreter configuration stands for under the factory `F`. -/
@[expose] def ICFGConfig.abs {l CmdT : Type} {P : PureExpr} [InterpLang P] [DecidableEq P.Ident]
    (F : P.Factory) : ICFGConfig l CmdT P → CFGConfig l CmdT P
  | .atBlock g t ρ => .atBlock g t (ρ.abs F)
  | .inBlock g t cs tr ρ => .inBlock g t cs tr (ρ.abs F)
  | .terminal ρ => .terminal (ρ.abs F)

/-- The store of a CFG interpreter configuration denotes under `F`, and its environment carries
    the runtime factory of `F`. -/
@[expose] def ICFGConfig.Denoting {l CmdT : Type}
    {P : PureExpr} [InterpLang P] [DecidableEq P.Ident]
    (F : P.Factory) (c : ICFGConfig l CmdT P) : Prop :=
  RStore.Denoting F c.env.store.get ∧ c.env.factory = InterpLang.rfactory F

/-- The CFG interpreter configuration `c` denotes the `CFGConfig` `d` under `F`. -/
@[expose] def ICFGConfig.Denotes {l CmdT : Type} {P : PureExpr} [InterpLang P] [DecidableEq P.Ident]
    (F : P.Factory) (c : ICFGConfig l CmdT P) (d : CFGConfig l CmdT P) : Prop :=
  c.Denoting F ∧ c.abs F = d

/-- A monadic command stepper for the CFG driver: execute one command against
    the running store (emitting events / drawing nondeterminism through the
    monad), returning the updated store.  For Core this is `stepBaseCmdStore`. -/
abbrev StepCmdStoreM (P : PureExpr) [InterpLang P] (CmdT : Type) (m : Type → Type) :=
  Nat → InterpLang.RFactory P → IStore P → CmdT → m (IStore P)

/-- The command stepper over stores of a configuration stepper `step`: run `step` from the
    environment of the store and the factory, and return the store of the environment of the
    configuration it produces. -/
abbrev StepCmdM.toStore {P : PureExpr} [InterpLang P] {CmdT : Type} {m : Type → Type} [Monad m]
    (step : StepCmdM P CmdT m) : StepCmdStoreM P CmdT m :=
  fun k f σ c => step k { store := σ, factory := f } c >>= fun r => pure r.getEnv.store

/-- One CFG step, mirroring `StepCFGE`.  The CFG and the environment come from the
    configuration, as in `StepCFGE`; `fuel` is the bounded-eval budget for a `condGoto` guard
    and is threaded to `stepCmd`, which runs each command at the environment's factory and
    store.  A `condGoto` guard is read as a Boolean literal up to metadata
    (`InterpLang.boolLit?`); a value that is neither `HasBool.tt` nor `HasBool.ff` is resolved by
    `InterpEffects.branch`, as `resolveGuard` resolves an `ite` guard. -/
def stepInterpCFG (stepCmd : StepCmdStoreM P CmdT m) (fuel : Nat) :
    ICFGConfig l CmdT P → m (ICFGConfig l CmdT P)
  | .atBlock g t ρ =>
    match List.lookup t g.blocks with
    | some b => pure (.inBlock g t b.cmds b.transfer ρ)
    | none => throw .unsupportedMissingBlockLabel
  | .inBlock g t (c :: cs) tr ρ => do
    let σ' ← stepCmd fuel ρ.factory ρ.store c
    pure (.inBlock g t cs tr { ρ with store := σ' })
  | .inBlock g _t [] tr ρ =>
    match tr with
    | .condGoto c tlbl elbl _ =>
      match InterpLang.boundedEval (P := P) fuel ρ.factory ρ.store.get c with
      | some v =>
        match InterpLang.boolLit? v with
        | some true => pure (.atBlock g tlbl ρ)
        | some false => pure (.atBlock g elbl ρ)
        | none => do
          let b ← InterpEffects.branch (P := P) ρ.factory ρ.store.get v
          pure (.atBlock g (if b then tlbl else elbl) ρ)
      | none => throw .expressionDidNotEvaluate
    | .finish _ => pure (.terminal ρ)
  | .terminal ρ => pure (.terminal ρ)

/-- The CFG driver: step until a `.terminal` config or fuel runs out.
    Mirrors `runInterp` (structural fuel recursion). -/
def runInterpCFG (stepCmd : StepCmdStoreM P CmdT m) :
    Nat → ICFGConfig l CmdT P → m (ICFGConfig l CmdT P)
  | fuel, cfgc =>
    match cfgc with
    | .terminal _ => pure cfgc
    | _ =>
      match fuel with
      | 0 => throw .replayFuelExhausted
      | fuel + 1 => do
        let next ← stepInterpCFG stepCmd (fuel + 1) cfgc
        runInterpCFG stepCmd fuel next

end -- public section

end Imperative
