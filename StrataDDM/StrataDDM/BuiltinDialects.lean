/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDDM.Elab.LoadedDialects
public import StrataDDM.BuiltinDialects.Init
public import StrataDDM.BuiltinDialects.StrataDDL
public import StrataDDM.BuiltinDialects.StrataHeader

public section
namespace StrataDDM.Elab.LoadedDialects

def builtin : LoadedDialects := .ofDialects! #[initDialect, headerDialect, StrataDDL]

end StrataDDM.Elab.LoadedDialects
end
