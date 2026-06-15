/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPython.Specs.Decls

meta section

open StrataPython.Specs

namespace DeclsTest

-- unionArray deduplicates
#guard (SpecType.unionArray default
    #[SpecType.intLiteral ⟨0, 0⟩ 0, SpecType.intLiteral ⟨0, 0⟩ 0]).intLits.size == 1

end DeclsTest
end
