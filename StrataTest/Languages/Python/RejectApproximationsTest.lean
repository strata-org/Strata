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
  match rejectableHole false "BinOp Div" (astRepr := "<ast>") with
  | .ok ⟨.Hole, _⟩ => true
  | _ => false

-- rejectableHole true -> raises unsupportedConstruct with [approximation] tag
#guard
  match rejectableHole true "BinOp Div" (astRepr := "<ast>") with
  | .error (.unsupportedConstruct msg _) =>
      msg.startsWith "[approximation]" && (msg.splitOn "BinOp Div").length > 1
  | _ => false

-- rejectableDrop false -> no-op
#guard
  match rejectableDrop false "raise" (astRepr := "<ast>") with
  | .ok () => true
  | _ => false

-- rejectableDrop true -> raises with "silently dropped" wording
#guard
  match rejectableDrop true "raise" (astRepr := "<ast>") with
  | .error (.unsupportedConstruct msg _) =>
      msg.startsWith "[approximation]"
        && (msg.splitOn "silently dropped").length > 1
  | _ => false

-- astRepr longer than 200 chars is truncated with an ellipsis
#guard
  let big := String.ofList (List.replicate 500 'x')
  match rejectableHole true "huge" (astRepr := big) with
  | .error (.unsupportedConstruct _ payload) =>
      payload.length < big.length && payload.endsWith "…"
  | _ => false

-- a `source` is preferred over the AST repr for the diagnostic payload
#guard
  let fr : Strata.FileRange := ⟨.file "f.py", ⟨⟨10⟩, ⟨20⟩⟩⟩
  match rejectableHole true "x" (source := some fr) (astRepr := "huge") with
  | .error (.unsupportedConstruct _ payload) =>
      (payload.splitOn "huge").length == 1
        && (payload.splitOn "f.py").length > 1
  | _ => false

end Strata.Python.RejectApproximationsTest
