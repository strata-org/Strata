/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.GOTO.CFGToCProverGOTO
public import Strata.Languages.GOTO.CoreToCProverGOTO
public import Strata.Languages.GOTO.LambdaToCProverGOTO
public import Strata.Languages.GOTO.Program
public import Strata.Languages.GOTO.ToCProverGOTO

/-! # GOTO

The GOTO intermediate language (CBMC's `CProverGOTO` program model) together
with the translations that produce it from other Strata languages. Following
the principle that `X → GOTO` translations live with GOTO, this aggregates the
IR (`SourceLocation`, `Type`, `Expr`, `Code`, `Instruction`, `Program`) and the
`Imperative`/`Lambda`/CFG → GOTO translations.

Serializing GOTO into CBMC's JSON format, building CBMC symbol tables, and
invoking the tool live separately under `Strata.Backends.CBMC`.
-/
