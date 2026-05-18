/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Util.FileRange

/-! # Diagnostic Classifier

Priority order: StrataBug > UserError > NotYetImplemented.
Empty or warnings-only batches fall through to `internalError`.
-/

public section
namespace Strata

inductive DiagnosticOutcome where
  | internalError
  | userError
  | knownLimitation
  deriving DecidableEq, Repr, Inhabited

def classifyDiagnostics (diags : List DiagnosticModel) : DiagnosticOutcome :=
  if diags.any (fun d => d.type == DiagnosticType.StrataBug) then
    .internalError
  else if diags.any (fun d => d.type == DiagnosticType.UserError) then
    .userError
  else if diags.any (fun d => d.type == DiagnosticType.NotYetImplemented) then
    .knownLimitation
  else
    .internalError

end Strata
end
