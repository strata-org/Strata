/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Main BoogieMinimal dialect definition
-- This is a minimal test dialect to validate DDM datatype genericity.
-- Unlike Boogie, BoogieMinimal:
-- - Uses integer indexers instead of boolean testers
-- - Does NOT generate field accessors (no perField template)

import Strata.Languages.BoogieMinimal.DDMTransform.DatatypeConfig
import Strata.Languages.BoogieMinimal.DDMTransform.Parse
import Strata.Languages.BoogieMinimal.DDMTransform.Translate

namespace Strata
namespace BoogieMinimal

-- Re-export key types and functions
export Strata (BoogieMinimalDatatypeConfig defaultBoogieMinimalDatatypeConfig)

end BoogieMinimal
end Strata
