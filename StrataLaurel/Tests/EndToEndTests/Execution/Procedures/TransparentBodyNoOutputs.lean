/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # A transparent body with no outputs and a discarded tail expression

`transparentBodyNoOuts` declares no outputs, so its trailing `3` is a value nothing can
receive — and the procedure is transparent, so a caller inlines that body rather than reasoning
from a contract. The pair is what makes the shape interesting: `TransparencyPass` has to build an
`$asFunction` twin for a procedure with no output to carry, and the discarded tail has to survive
as far as `LaurelToCoreSchemaPass`, which is what finally binds it. `FunctionalRewrite` leaves the
twin alone.

This runs the FULL pipeline. Resolution accepts the shape and reports nothing, so a
resolution-only harness would pass here no matter what the later passes did with it — the same
program with `assert false` and no annotation also passes under `testLaurelResolution`, while the
verifier reports `assertion does not hold`. The case therefore lives in `Execution` rather than
`Resolution`: what it asserts is that the shape survives lowering, which only the pipeline can
show. -/

-- Both interpreters run it too: the inlined transparent body is executed as well as verified,
-- so a `TransparencyPass` result that type-checked but computed the wrong thing would show up
-- here as a runtime failure rather than only as a proof that went through.
#eval testLaurelExecution {} <|
#strata
program Laurel;

procedure transparentBodyNoOuts()
  entry
{
  assert true;
  3
};

procedure transparentProcedureCaller() entry opaque {
  transparentBodyNoOuts()
};
#end
