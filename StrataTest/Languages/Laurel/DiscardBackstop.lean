/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Pipeline.Messages
import Strata.Languages.Laurel.LaurelCompilationPipeline

open Strata Strata.Laurel

/-
  Unit test for the Laurel-to-Core soundness backstop
  `ensureDiscardDiagnosed`: a discarded Core program (`none`) must never
  reach the verifier without an error diagnostic (which would be reported
  as a vacuous "0 errors / verified"). The backstop must:
-/

-- fire when the program is discarded and no error was reported
#guard (ensureDiscardDiagnosed (programPresent := false) []).length == 1
#guard (ensureDiscardDiagnosed (programPresent := false) []).any (fun d => d.kind != .warning)
-- stay dormant when the program is present
#guard (ensureDiscardDiagnosed (programPresent := true) []).isEmpty
-- not double-report when an error is already present
#guard (ensureDiscardDiagnosed (programPresent := false)
          [Message.fromString "e" .userError]).length == 1
-- still fire alongside a pre-existing WARNING (a warning is not an error)
#guard (ensureDiscardDiagnosed (programPresent := false)
          [Message.fromString "w" .warning]).length == 2
