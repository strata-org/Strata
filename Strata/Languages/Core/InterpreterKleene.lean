/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CallAwareSemantics
public import Strata.Languages.Core.InterpreterReplay
public import Strata.Languages.Core.InterpreterEval
public import Strata.Languages.Core.InterpreterCallSound
public import Strata.DL.Imperative.InterpreterKleeneCall

/-! # Core instantiation of the call-aware monadic Kleene interpreter

`runCoreInterpKleene` specialises the call-aware Kleene driver
`Imperative.Calls.runCallInterpKleene` to the Core parameters — `P = Expression`,
command type `Command = CmdExt Expression`, procedure headers `Procedure.Header` —
so a Kleene `.cmd` holding a `.call` runs the callee body to completion exactly as
the reference relation `Imperative.StepKleeneExtStarE` prescribes.  It is
monad-generic, so it runs under both `InterpEffects Expression` instances
(`ReplayM`, `EvalM`).  Its soundness and completeness theorems are in
`InterpreterKleeneProps.lean`. -/

namespace Core

open Imperative Imperative.Calls

public section

/-- The Core call-aware monadic Kleene interpreter: run a Core `KleeneStmt` program (as an
    `IKleeneConfig`) under any `InterpEffects Expression` instance, the call-aware
    `Imperative.Calls.stepKleeneCmd π` executing each atomic command (a base
    command via `stepBaseCmdStore`, a `.call` by running the callee body), nesting at most
    `maxCallDepth` calls. -/
def runCoreInterpKleene {m : Type → Type} [Monad m] [InterpEffects Expression m]
    [MonadExcept StopReason m] (π : String → Option Procedure)
    (fuel : Nat) (cfgc : IKleeneConfig Expression Command)
    (maxCallDepth : Nat := defaultMaxCallDepth) :
    m (IKleeneConfig Expression Command) :=
  Imperative.Calls.runCallInterpKleene (Hdr := Procedure.Header) π fuel cfgc maxCallDepth

/-! ## Elaboration smoke checks -/

/-- The Core Kleene driver elaborates under the replay instance. -/
example (π : String → Option Procedure) (fuel : Nat) (c : IKleeneConfig Expression Command) :
    ReplayM Expression (IKleeneConfig Expression Command) :=
  runCoreInterpKleene (m := ReplayM Expression) π fuel c

/-- The Core Kleene driver elaborates under the faithful-legacy eval instance. -/
example (π : String → Option Procedure) (fuel : Nat) (c : IKleeneConfig Expression Command) :
    EvalM (IKleeneConfig Expression Command) :=
  runCoreInterpKleene (m := EvalM) π fuel c

end -- public section

end Core
