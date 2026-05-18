/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Util.DiagnosticClassifier
import Strata.Util.DiagnosticClassifier

open Strata

def mkDiag (t : DiagnosticType) : DiagnosticModel :=
  { fileRange := FileRange.unknown, message := "test", type := t }

-- Individual arms
#guard classifyDiagnostics [mkDiag .StrataBug] = .internalError
#guard classifyDiagnostics [mkDiag .UserError] = .userError
#guard classifyDiagnostics [mkDiag .NotYetImplemented] = .knownLimitation

-- Priority: StrataBug > UserError > NotYetImplemented
#guard classifyDiagnostics [mkDiag .UserError, mkDiag .StrataBug] = .internalError
#guard classifyDiagnostics [mkDiag .StrataBug, mkDiag .UserError] = .internalError
#guard classifyDiagnostics [mkDiag .NotYetImplemented, mkDiag .UserError] = .userError
#guard classifyDiagnostics
  [mkDiag .NotYetImplemented, mkDiag .UserError, mkDiag .StrataBug] = .internalError

-- Defensive fallthrough
#guard classifyDiagnostics [] = .internalError
#guard classifyDiagnostics [mkDiag .Warning] = .internalError
#guard classifyDiagnostics [mkDiag .Warning, mkDiag .Warning] = .internalError
