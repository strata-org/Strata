/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.DDM.Elab.LoadedDialects
public import Strata.DDM.BuiltinDialects.Init
public import Strata.DDM.BuiltinDialects.StrataDDL
public import Strata.DDM.BuiltinDialects.StrataHeader

public section
namespace Strata.Elab.LoadedDialects

def builtin : LoadedDialects := .ofDialects! #[initDialect, headerDialect, StrataDDL]

end Strata.Elab.LoadedDialects
end
