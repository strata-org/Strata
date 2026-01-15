/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.SMT.DDMTransform.Translate

/-!
# SMT Term Formatting

Formats SMT terms to SMT-LIB syntax using the SMT dialect's pretty-printer.

This module uses `SMTDDM.toString` which translates SMT terms to the SMT dialect's
AST and then uses the dialect's formatter to generate SMT-LIB strings.
-/

namespace Strata.B3.Verifier

open Strata.SMT

/-- Format SMT term to SMT-LIB syntax using the SMT dialect's pretty-printer -/
def formatTermDirect (t : Term) : String :=
  match SMTDDM.toString t with
  | .ok s => s
  | .error msg => s!"(error: {msg})"

end Strata.B3.Verifier
