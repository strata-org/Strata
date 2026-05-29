/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.CoreMatch.CoreMatch
public import Strata.Languages.CoreMatch.ToCore
public import Strata.Languages.CoreMatch.DDMTransform.Translate
public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Verifier
public import Strata.Languages.Core.EntryPoint

/-!
Public entry points for the CoreMatch dialect's source-to-Core
pipeline.
-/

namespace Strata.CoreMatch.Verify

open Core

public section

/-- Lower an already-translated `MProgram` to a `Core.Program`. -/
@[expose]
def toCore (prog : Strata.CoreMatch.MProgram) : Core.Program :=
  Strata.CoreMatch.ToCore.compileProgram prog

/-- Parse a `Strata.Program` against the CoreMatch dialect and lower
it all the way to a `Core.Program`. -/
@[expose]
def parseToCore (prog : Strata.Program) (fileName : String := "")
    : Except DiagnosticModel Core.Program :=
  Strata.CoreMatch.Translate.toCoreProgram prog fileName

end

end Strata.CoreMatch.Verify
