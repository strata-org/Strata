/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Logic.Hoare
public import Strata.Languages.Core.Logic.HoareTotal

/-! # Hoare Logic for unstructured Core CFGs

Core-specific wrappers around the language-generic Hoare triples, instantiated
with `EventLang.coreCFG`. `Hoare.TripleUnstructuredWith` and `Hoare.TripleUnstructured`
are the CFG counterparts of `TripleWith` and `Triple` in
`Strata.Languages.Core.Logic.Hoare`; `HoareTotal.TripleUnstructuredWith` and
`HoareTotal.TripleUnstructured` are their total-correctness counterparts, for
`Strata.Languages.Core.Logic.HoareTotal`.
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

/-- **Core Hoare triple over an unstructured CFG**, with conditions read by evaluation
    in runtime factories over `factory`. The default is `Core.Factory`. -/
@[expose] def TripleUnstructured (params : InitEnvWFParams)
    (Pre : Imperative.Env Expression → Prop) (cfg : Core.DetCFG)
    (Post : Imperative.Env Expression → Prop)
    (factory : Lambda.Factory CoreLParams := Core.Factory) : Prop :=
  TripleUnstructuredWith π (DenoteBasedInterp factory) params Pre cfg Post

/-
TODO: Add a block-local proof rule for `TripleUnstructured`. Attach a
precondition to each basic block and prove that every execution of each block
starting from its precondition reaches a successor block whose precondition is
satisfied. From those local obligations, derive the Hoare triple for the full
CFG.
-/

end Hoare

namespace HoareTotal

variable (π : String → Option Procedure)

/-- Core CFG total-correctness Hoare triple with an explicit event-condition
    interpretation. -/
@[expose] def TripleUnstructuredWith (conditionInterp : ConditionInterp Expression)
    (params : InitEnvWFParams)
    (Pre : Imperative.Env Expression → Prop) (cfg : Core.DetCFG)
    (Post : Imperative.Env Expression → Prop) : Prop :=
  Strata.Logic.HoareTotal.TripleWith (EventLang.coreCFG π)
    conditionInterp params Pre cfg Post

/-- **Core total-correctness Hoare triple over an unstructured CFG**, with conditions read
    by evaluation in runtime factories over `factory`. The default is `Core.Factory`. -/
@[expose] def TripleUnstructured (params : InitEnvWFParams)
    (Pre : Imperative.Env Expression → Prop) (cfg : Core.DetCFG)
    (Post : Imperative.Env Expression → Prop)
    (factory : Lambda.Factory CoreLParams := Core.Factory) : Prop :=
  TripleUnstructuredWith π (DenoteBasedInterp factory) params Pre cfg Post

end HoareTotal

end Core.Logic

end -- public section
