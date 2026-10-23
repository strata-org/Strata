/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Logic.Hoare

/-! # Hoare Logic for unstructured Core CFGs

Core-specific wrappers around the language-generic Hoare triple, instantiated
with `EventLang.coreCFG`. These are the CFG counterparts of `TripleWith` and
`Triple` in `Strata.Languages.Core.Logic.Hoare`.
-/

public section

namespace Core.Logic

open Core Imperative Strata.Logic Imperative.Logic

namespace Hoare

variable (π : String → Option Procedure)

/-- Core CFG Hoare triple with an explicit event-condition interpretation. -/
@[expose] def TripleUnstructuredWith (conditionInterp : ConditionInterp Expression)
    (params : InitEnvWFParams)
    (Pre : Imperative.Env Expression → Prop) (cfg : Core.DetCFG)
    (Post : Imperative.Env Expression → Prop) : Prop :=
  Strata.Logic.Hoare.TripleWith (EventLang.coreCFG π)
    conditionInterp params Pre cfg Post

/-- **Core Hoare triple over an unstructured CFG.** -/
@[expose] def TripleUnstructured (params : InitEnvWFParams)
    (Pre : Imperative.Env Expression → Prop) (cfg : Core.DetCFG)
    (Post : Imperative.Env Expression → Prop) : Prop :=
  ∀ model : Lambda.Interp Core.Factory,
    TripleUnstructuredWith π (DenoteBasedInterp model) params Pre cfg Post

/-
TODO: Add a block-local proof rule for `TripleUnstructured`. Attach a
precondition to each basic block and prove that every execution of each block
starting from its precondition reaches a successor block whose precondition is
satisfied. From those local obligations, derive the Hoare triple for the full
CFG.
-/

end Hoare

end Core.Logic

end -- public section
