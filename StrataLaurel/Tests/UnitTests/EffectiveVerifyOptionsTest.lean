/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Laurel prunes axioms with `Precise`, asking that each goal see only the axioms it needs. Under
`--incremental` it therefore prunes exactly, so a live solver never keeps an axiom a goal drops,
and a Laurel verdict does not depend on `--incremental`.
-/

import StrataLaurel.Implementation.LaurelCompilationPipeline

namespace Strata.Laurel

private def incrementalOptions : LaurelVerifyOptions :=
  { verifyOptions := { Core.VerifyOptions.default with incremental := true } }

#guard (effectiveCoreVerifyOptions incrementalOptions).removeIrrelevantAxioms == .Precise
#guard (effectiveCoreVerifyOptions incrementalOptions).exactPruning

end Strata.Laurel
