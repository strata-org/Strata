/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

-- We do not allow variable shadowing in Strata Core.

def noShadowPgm1 :=
#strata
program Core;
var g : int;
procedure Test() returns ()
{
  var g : bool;
};
#end

/--
error:  ❌ Type checking error.
Variable g of type int already in context.
-/
#guard_msgs in
#eval verify noShadowPgm1 (options := Options.quiet)

def noShadowPgm2 :=
#strata
program Core;
procedure Test() returns ()
{
  var g : bool;
  var g : int;
};
#end

/--
error:  ❌ Type checking error.
Variable g of type bool already in context.
-/
#guard_msgs in
#eval verify noShadowPgm2 (options := Options.quiet)

---------------------------------------------------------------------
