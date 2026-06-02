/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-!
# Approximation diagnostics

Single source of truth for the wording and `[approximation]` prefix used by
both the Python→Laurel translator and the PySpec parser when an unsupported
Python construct is approximated (or silently dropped) under lax mode and
would be rejected as an error under `--reject-approximations`. Keeping the
prefix in one place lets downstream tooling filter on it reliably.
-/

public section

namespace Strata.Python.Approximation

/-- Kind of approximation site. -/
inductive Kind where
  /-- The translator emits a havoc'd `Hole` instead of a faithful translation. -/
  | hole
  /-- The translator silently drops the construct from the lowered program. -/
  | drop
  /-- The PySpec parser fell back to `.placeholder` and emitted a warning;
      strict mode promotes that warning to an error. -/
  | warningPromotion
  deriving DecidableEq, Repr

/-- The `[approximation] ` prefix that downstream tooling filters on. Must
    not change without coordinating with consumers. -/
def prefixTag : String := "[approximation] "

/-- Render a strict-mode approximation diagnostic. The `construct` argument
    names the surface form (e.g. `"BinOp Div"`) for `.hole` and `.drop`; for
    `.warningPromotion`, it carries the original warning message verbatim. -/
def render : Kind → (construct : String) → String
  | .hole, c =>
    s!"{prefixTag}{c} is approximated as Hole; not in the sound subset"
  | .drop, c =>
    s!"{prefixTag}{c} is silently dropped by current translation; not in the sound subset"
  | .warningPromotion, msg =>
    s!"{prefixTag}{msg}"

end Strata.Python.Approximation

end
