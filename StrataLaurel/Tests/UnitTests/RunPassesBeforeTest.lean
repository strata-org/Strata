/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
`runPassesBefore` refuses a pass that `laurelPipeline` does not contain, such as one not yet wired in.
No test that uses it reaches that refusal, so it is pinned here.
-/

import StrataLaurel.Implementation.LaurelCompilationPipeline

namespace Strata.Laurel

private def notWiredIn : LaurelPass :=
  LaurelPass.onUnordered { name := "NotWiredIn", documentation := "Not in laurelPipeline." }
    (fun _ p _ => (p, [], {}))

/-- error: runPassesBefore: 'NotWiredIn' is not in laurelPipeline -/
#guard_msgs in
#eval do
  let _ ← runPassesBefore notWiredIn {} { staticProcedures := [], staticFields := [], types := [] }

end Strata.Laurel
