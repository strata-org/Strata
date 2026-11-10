/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CallAwareSemantics
public import Strata.Languages.Core.InterpreterReplay
public import Strata.Languages.Core.InterpreterCallSound
public import Strata.DL.Imperative.InterpreterCFGCallSound

/-! # Core instantiation of the call-aware monadic CFG interpreter

`runCoreInterpCFG` specialises `Imperative.runInterpCFG` to the Core parameters —
`P = Expression`, block label `String`, and command type `Command = CmdExt
Expression` — with the call-aware store-stepper `Imperative.Calls.cfgStepCmd π` as
the per-command stepper, so a `.call` inside a CFG block runs the callee body to
completion.  It is generic in the monad, running under every `InterpEffects
Expression` instance (`ReplayM` / `EvalM`), mirroring how `runCoreInterp`
(structured) instantiates `runInterp`.  Its soundness and completeness theorems are in
`InterpreterCFGProps.lean`. -/

namespace Core

open Imperative Imperative.Calls

public section

/-- The Core call-aware CFG driver: run a deterministic Core CFG under any
    `InterpEffects` instance, `Calls.cfgStepCmd π maxCallDepth` executing each block command
    (running a `.call`'s callee body to completion, nesting at most `maxCallDepth` calls). -/
def runCoreInterpCFG {m : Type → Type} [Monad m] [InterpEffects Expression m]
    [MonadExcept StopReason m]
    (π : String → Option Procedure) (fuel : Nat)
    (cfgc : ICFGConfig String Command Expression)
    (maxCallDepth : Nat := defaultMaxCallDepth) :
    m (ICFGConfig String Command Expression) :=
  runInterpCFG (cfgStepCmd π maxCallDepth) fuel cfgc

/-! ## Elaboration smoke checks

The Core CFG driver is monad-generic; these `example`s confirm it elaborates
against the available `InterpEffects Expression` instances — `ReplayM` and
`EvalM`. -/

/-- Elaborates under the replay instance. -/
example (π : String → Option Procedure) (fuel : Nat)
    (c : ICFGConfig String Command Expression) :
    ReplayM Expression (ICFGConfig String Command Expression) :=
  runCoreInterpCFG (m := ReplayM Expression) π fuel c

/-- Elaborates under the faithful-legacy eval instance. -/
example (π : String → Option Procedure) (fuel : Nat)
    (c : ICFGConfig String Command Expression) :
    EvalM (ICFGConfig String Command Expression) :=
  runCoreInterpCFG (m := EvalM) π fuel c

end -- public section

end Core
