/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
meta import Strata.Languages.Python.CorePrelude
meta import Strata.DDM.Ion


meta section

namespace Strata.Python

/--
Test that the Python CorePrelude can be serialized to Ion format and
deserialized back without loss of information.
-/
private def testCorePreludeRoundTrip : Bool :=
  let prelude := Python.corePrelude
  let bytes := prelude.toIon
  match Program.fromIon Strata.Core_map Strata.Core.name bytes with
  | .ok pgm => pgm.commands.size == prelude.commands.size
  | .error _ => false

#guard testCorePreludeRoundTrip

end Strata.Python
