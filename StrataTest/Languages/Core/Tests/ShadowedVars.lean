/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section

---------------------------------------------------------------------
namespace Strata

-- We do not allow variable shadowing in Strata Core.

def noShadowPgm1 :=
#strata
program Core;
procedure Test(g : int)
{
  var g : bool;
};
#end

/--
error: ❌ Type checking error.
Variable g of type int already in context.
-/
#guard_msgs in
#eval Core.verify noShadowPgm1 (options := .quiet)

def noShadowPgm2 :=
#strata
program Core;
procedure Test()
{
  var g : bool;
  var g : int;
};
#end

/--
error: ❌ Type checking error.
Variable g of type bool already in context.
-/
#guard_msgs in
#eval Core.verify noShadowPgm2 (options := .quiet)

---------------------------------------------------------------------

end Strata

end
