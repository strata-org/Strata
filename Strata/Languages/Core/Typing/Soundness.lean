/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Typing.Soundness.TypingAssumptions
public import Strata.Languages.Core.Typing.Soundness.Command
public import Strata.Languages.Core.Typing.Soundness.TypeDecl
public import Strata.Languages.Core.Typing.Soundness.Function
public import Strata.Languages.Core.Typing.Soundness.Statement
public import Strata.Languages.Core.Typing.Soundness.StatementOutput
public import Strata.Languages.Core.Typing.Soundness.Procedure
public import Strata.Languages.Core.Typing.Soundness.RecFuncBlockInversion
public import Strata.Languages.Core.Typing.Soundness.RecFuncBlock
public import Strata.Languages.Core.Typing.Soundness.Program
public import Strata.Languages.Core.Typing.Soundness.Core

/-! # Soundness of the Core typechecker
Every program `Core.typeCheck` accepts satisfies `ProgramHasType`, and the program it returns
is well typed with valid names: `Core.typeCheck_sound` and `Core.typeCheck_sound_output`. -/
