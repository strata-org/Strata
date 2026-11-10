/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterKleene
public import Strata.DL.Imperative.InterpreterCall

/-! # Call-aware Kleene command stepper

The Kleene driver `stepInterpKleene` (`InterpreterKleene.lean`) is command-generic:
it takes a store-to-store command stepper
`Nat → InterpLang.RFactory P → IStore P → CmdT → m (IStore P)` (`StepCmdStoreM`).  To run a Kleene
program whose atomic commands are `CmdExt P` (base commands and `.call`), this
module adapts the structured call stepper `Calls.stepCmd π`
(`InterpreterCall.lean`), which runs a callee body to completion, to that store
interface by projecting the resulting (always-terminal) configuration back to its
store.  A `.call` inside a Kleene `.cmd` thus runs the callee body exactly as the
reference relation `EvalCmdExtE π` prescribes, while the Kleene driver
stays call-agnostic. -/

namespace Imperative

public section

namespace Calls

variable {P : PureExpr}
variable [DecidableEq P.Ident] [HasOldIdent P]
  {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]
variable [HasBool P] [DecidableEq P.Expr] [InterpLang P] [HasFvar P]

/-- The call-aware Kleene command stepper at call-depth budget `depth`: run
    `Calls.stepCmd π depth` from the `(store, factory)` env and project the resulting terminal
    configuration to its store. -/
def stepKleeneCmd {m : Type → Type} [Monad m] [InterpEffects P m] [MonadExcept StopReason m]
    (π : String → Option (Procedure P (CmdExt P) Hdr)) (depth : Nat) :
    StepCmdStoreM P (CmdExt P) m :=
  StepCmdM.toStore (Calls.stepCmd π depth)

/-- The call-aware Kleene driver: `runInterpKleene` over `stepKleeneCmd π maxCallDepth`,
    nesting at most `maxCallDepth` calls. -/
@[expose] def runCallInterpKleene {m : Type → Type} [Monad m] [InterpEffects P m]
    [MonadExcept StopReason m] (π : String → Option (Procedure P (CmdExt P) Hdr))
    (fuel : Nat) (cfg : IKleeneConfig P (CmdExt P))
    (maxCallDepth : Nat := defaultMaxCallDepth) : m (IKleeneConfig P (CmdExt P)) :=
  runInterpKleene (stepKleeneCmd π maxCallDepth) fuel cfg

end Calls

end -- public section

end Imperative
