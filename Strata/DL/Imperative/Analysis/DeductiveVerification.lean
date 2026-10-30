/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Analysis.Verdict

/-! # Deductive verification

Deductive verification of a program with entries `E` in event languages is a
report giving each assertion a `Verdict` that is correct: it proves assertions
valid, may show them failed from an entry, and may say it does not know. It is
stated once for every family of event languages and condition interpretation,
and instantiated for Core in
`Strata.Languages.Core.Analysis.DeductiveVerification`.
-/

public section

namespace Strata.Analysis

open Imperative Strata.Logic

variable {P : PureExpr} {Idx : Type} {EL : Idx → EventLang P (Event P)}

/-- **Deductive verification** of `p`, with conditions read through `I`: every
    verdict of `report` is correct. -/
@[expose] def DeductiveVerification (I : ConditionInterp P) (E : ProgramEntries EL)
    (p : E.Program) (report : AssertId P → Verdict E.Entry) : Prop :=
  ∀ a, VerdictCorrect I E p a (report a)

end Strata.Analysis

end -- public section
