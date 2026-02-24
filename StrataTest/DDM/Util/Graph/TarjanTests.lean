/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DDM.Util.Graph.Tarjan

namespace Strata.OutGraph.Tests

open Strata.OutGraph

#guard tarjan (.ofEdges! 5 [(0, 1), (1, 2), (2, 3), (2, 0), (2, 4), (4, 3), (4, 1)]) == #[#[0, 1, 2, 4], #[3]]

end Strata.OutGraph.Tests
