/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Python.Specs.Decls

open Strata.Python.Specs

namespace DeclsTest

-- unionArray deduplicates
#guard (SpecType.unionArray default
    #[SpecType.intLiteral ⟨0, 0⟩ 0, SpecType.intLiteral ⟨0, 0⟩ 0]).intLits.size == 1

end DeclsTest
