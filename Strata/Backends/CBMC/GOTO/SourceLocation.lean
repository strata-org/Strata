/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

namespace CProverGOTO
-------------------------------------------------------------------------------

/-- Source location information -/
structure SourceLocation where
  file : String
  line : Nat
  column : Nat := 0
  function : String
  workingDir : String
  comment : String
deriving Repr, DecidableEq, Inhabited

def SourceLocation.nil : SourceLocation :=
  { file := "", line := 0, column := 0, function := "", workingDir := "", comment := "" }

instance : ToString SourceLocation where
  toString loc :=
    if loc.file.isEmpty then ""
    else s!"{loc.file}:{loc.line}:{loc.column}"

-------------------------------------------------------------------------------
