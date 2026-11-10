/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Interpreter
public import Strata.DL.Lambda.FactoryWF
import Strata.Languages.Core.InterpreterReplayTactics

/-! # Well-formedness of a counterexample's configuration

Key definitions: `CfgWF` and `CexWF`, which require the factory of a configuration to be
well-formed (`FactoryOK`) and every store to be closed (`StoreClosed`), so that
evaluating an expression depends only on the values of its free variables. Lemmas about
these definitions are in `Core/ConfigWFProps.lean`. -/

namespace Core

open Imperative

public section

/-- A well-formed factory on which the Boolean values are `true` and `false`
    (no constructor produces a Boolean). -/
@[expose] def FactoryOK (F : @Lambda.Factory CoreLParams) : Prop :=
  Lambda.FactoryWF F ∧ Lambda.Factory.ConstrsNotBool F

/-- Every value of the runtime store is closed. -/
@[expose] def StoreClosed (σ : RStore Expression) : Prop :=
  ∀ x v, σ x = some v → Lambda.LExpr.LExpr.getVars v = []

/-- The factory and the store of an environment are well-formed. -/
@[expose] def EnvWF (ρ : Imperative.IEnv Expression) : Prop :=
  FactoryOK ρ.factory ∧ StoreClosed ρ.store.get

/-- The factory and every runtime store the interpreter configuration holds, active or enclosing,
    are well-formed. -/
@[expose] def CfgWF {CmdT : Type} : IConfig Expression CmdT → Prop
  | .stmt _ ρ => EnvWF ρ
  | .stmts _ ρ => EnvWF ρ
  | .terminal ρ => EnvWF ρ
  | .exiting _ ρ => EnvWF ρ
  | .block _ fr inner => StoreClosed fr.parent.get ∧ CfgWF inner
  | .seq inner _ => CfgWF inner
  | .seqs inner _ => CfgWF inner

/-- Well-formedness of a counterexample's start configuration. -/
@[expose] def CexWF {CmdT : Type} (c : CexA Expression CmdT) : Prop :=
  CfgWF c.cfg

end -- public section

end Core
