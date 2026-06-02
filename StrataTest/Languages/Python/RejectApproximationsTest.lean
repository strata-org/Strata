/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Python.Approximation
import Strata.Languages.Python.PythonToLaurel

/-! # `--reject-approximations` flag tests

Unit tests for the `rejectableHole` / `rejectableDrop` helpers: with
the flag off, they emit a `Hole` / no-op (lax behavior); with the flag
on, they raise `unsupportedConstruct` with an `[approximation]` tag.
-/

namespace Strata.Python.RejectApproximationsTest

open Strata.Python (rejectableHole rejectableDrop)
open Strata.Python.TranslationError

/-! ## Boolean dispatch lemmas

Pin the bool branch of `rejectableHole` / `rejectableDrop` so a future
refactor cannot accidentally reverse the strict/lax meaning. -/

theorem rejectableHole_strict (c : String) (r : String) :
    (rejectableHole (rejectApproximations := true) c (astRepr := r)).isOk = false := rfl

theorem rejectableHole_lax (c : String) (r : String) :
    (rejectableHole (rejectApproximations := false) c (astRepr := r)).isOk = true := rfl

theorem rejectableDrop_strict (c : String) (r : String) :
    (rejectableDrop (rejectApproximations := true) c (astRepr := r)).isOk = false := rfl

theorem rejectableDrop_lax (c : String) (r : String) :
    (rejectableDrop (rejectApproximations := false) c (astRepr := r)).isOk = true := rfl

/-- Strict mode produces a `.unsupportedConstruct` whose message starts
    with `Approximation.prefixTag`. Downstream tooling can rely on this. -/
theorem rejectableHole_strict_message (c : String) (r : String) :
    ∃ msg ast,
      rejectableHole (rejectApproximations := true) c (astRepr := r)
        = .error (.unsupportedConstruct msg ast)
      ∧ msg = Strata.Python.Approximation.render .hole c :=
  ⟨_, _, rfl, rfl⟩

theorem rejectableDrop_strict_message (c : String) (r : String) :
    ∃ msg ast,
      rejectableDrop (rejectApproximations := true) c (astRepr := r)
        = .error (.unsupportedConstruct msg ast)
      ∧ msg = Strata.Python.Approximation.render .drop c :=
  ⟨_, _, rfl, rfl⟩

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

/-! ## Shared `Approximation.render` format

All three approximation sites — `rejectableHole`, `rejectableDrop`, and
`Specs.lean`'s `specWarning` warning→error promotion — render through
`Strata.Python.Approximation.render`. The guards below pin the prefix
and per-kind wording so the three sites cannot drift apart. -/

open Strata.Python.Approximation (render Kind prefixTag)

#guard (render .hole "BinOp Div").startsWith prefixTag
#guard (render .drop "raise").startsWith prefixTag
#guard (render .warningPromotion "fallback to placeholder").startsWith prefixTag

#guard prefixTag == "[approximation] "

#guard ((render .hole "X").splitOn "approximated as Hole").length > 1
#guard ((render .drop "X").splitOn "silently dropped").length > 1
#guard render .warningPromotion "msg" == "[approximation] msg"

-- The strict-mode arm of `rejectableHole` shares wording with `render .hole`.
#guard
  match rejectableHole true "X" with
  | .error (.unsupportedConstruct msg _) => msg == render .hole "X"
  | _ => false

-- Likewise for `rejectableDrop`.
#guard
  match rejectableDrop true "X" with
  | .error (.unsupportedConstruct msg _) => msg == render .drop "X"
  | _ => false

end Strata.Python.RejectApproximationsTest
