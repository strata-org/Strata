/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def mapBranch :=
#strata
program Core;

datatype Any () {
  from_MapInt (as_MapInt : Map int int)
};

procedure testmap () returns ()
{
  var m : Map int int, v: Any;
  var k : Map int int;
  havoc m;
  v:= from_MapInt(m);
  if (Any..isfrom_MapInt(v)) {
    v := from_MapInt(m[2:=3]);
  }
  else {
    v := from_MapInt(m[2:=4]);
  }
  if (Any..isfrom_MapInt(v)) {
    v := from_MapInt(m[2:=3]);
  }
  else {
    v := from_MapInt(m[2:=4]);
  }
  k := Any..as_MapInt(v);
  assert [something]: k[2] == 3;
};
#end

/-- info: Obligation: something
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval verify mapBranch (options := Options.quiet)


end Strata
