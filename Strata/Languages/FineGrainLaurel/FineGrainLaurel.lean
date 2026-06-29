/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
-- FineGrainLaurel dialect definition, loaded from FineGrainLaurel.dialect.st
-- NOTE: Changes to FineGrainLaurel.dialect.st are not automatically tracked by the build system.
-- Update this file (e.g. this comment) to trigger a recompile after modifying FineGrainLaurel.dialect.st.
-- Last grammar change: added prodExit for break/continue control flow preservation.

module

public import StrataDDM.Integration.Lean
public meta import StrataDDM.Integration.Lean

namespace Strata.FineGrainLaurel

public section

#load_dialect "Strata/Languages/FineGrainLaurel/FineGrainLaurel.dialect.st"

#strata_gen FineGrainLaurel

end
