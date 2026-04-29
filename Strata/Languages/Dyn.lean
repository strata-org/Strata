/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

-- Aggregator: re-exports Dyn dialect submodules
-- TODO: Implement AST structure for dynamic Python-like language

public import Strata.Languages.Dyn.DDMTransform.Parse -- shake: keep
public import Strata.Languages.Dyn.DDMTransform.Translate -- shake: keep

public section

namespace Strata
namespace Dyn

-- TODO: Define AST structures

end Dyn
end Strata
