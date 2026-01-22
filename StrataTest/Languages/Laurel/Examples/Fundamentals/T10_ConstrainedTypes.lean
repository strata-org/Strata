/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Laurel

def program := r"
constrained nat = x: int where x >= 0 witness 0

composite Option {}
composite Some extends Option {
  value: int
}
composite None extends Option
constrained SealedOption = x: Option where x is Some || x is None witness None

procedure foo() returns (r: nat) {
}
"

-- Not working yet
-- #eval! testInput "ConstrainedTypes" program processLaurelFile
