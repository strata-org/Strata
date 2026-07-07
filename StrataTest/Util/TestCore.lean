/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import StrataDDM.Integration.Lean
public meta import Strata.Languages.Core
public meta import Strata.Languages.Core.DDMTransform.Translate

namespace StrataTest.Util

open Core
open Strata

public meta section

/-- Translate a `StrataDDM.SourcedProgram` (typically produced by `#strata`) to a
    Core `Program`, running the DDM->Core translation from a default initial
    state.

    Shared by the Core Transform tests so the one-liner isn't duplicated per
    file (see `StrataTest/Transform/ConstantPropagation.lean`). -/
def translate (t : StrataDDM.SourcedProgram) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

end -- public meta section

end StrataTest.Util
