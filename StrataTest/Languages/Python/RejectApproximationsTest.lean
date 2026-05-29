/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Python.PythonToLaurel

/-! # `--reject-approximations` flag tests

Unit tests for the `rejectableHole` / `rejectableDrop` helpers: with
the flag off, they emit a `Hole` / no-op (lax behavior); with the flag
on, they raise `unsupportedConstruct` with an `[approximation]` tag.
-/

namespace Strata.Python.RejectApproximationsTest

open Strata.Python (rejectableHole rejectableDrop)
open Strata.Python.TranslationError

-- rejectableHole false -> emits a Hole (lax behavior preserved)
#guard
  match rejectableHole false "BinOp Div" "<ast>" with
  | .ok ⟨.Hole, _⟩ => true
  | _ => false

-- rejectableHole true -> raises unsupportedConstruct with [approximation] tag
#guard
  match rejectableHole true "BinOp Div" "<ast>" with
  | .error (.unsupportedConstruct msg _) =>
      msg.startsWith "[approximation]" && (msg.splitOn "BinOp Div").length > 1
  | _ => false

-- rejectableDrop false -> no-op
#guard
  match rejectableDrop false "raise" "<ast>" with
  | .ok () => true
  | _ => false

-- rejectableDrop true -> raises with "silently dropped" wording
#guard
  match rejectableDrop true "raise" "<ast>" with
  | .error (.unsupportedConstruct msg _) =>
      msg.startsWith "[approximation]"
        && (msg.splitOn "silently dropped").length > 1
  | _ => false

end Strata.Python.RejectApproximationsTest
