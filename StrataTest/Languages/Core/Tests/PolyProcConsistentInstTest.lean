/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.Verifier
import StrataDDM.Integration.Lean.HashCommands

meta section
open StrataDDM (Program)

/-!
# Type parameters of a polymorphic procedure

In `p<a>(inout x : a, out y : a)`, `x`, `old x` and `y` have the same type,
both at a call and in the procedure's own contract.

These tests use `Strata.typeCheck`, which checks the program as written.
`Core.verify` type-checks only after `CallElim` and `GenOpaqueTypeParams`, when
no call or type parameter is left.
-/

namespace Strata.PolyProcConsistentInstTest

private def accepted (pgm : Program) : Bool :=
  (Strata.typeCheck Inhabited.default pgm (options := .quiet)).isOk

---------------------------------------------------------------------
-- Call site
---------------------------------------------------------------------

def callOutMatchPgm : Program :=
#strata
program Core;
procedure p<a>(x : a, out y : a);
procedure Test()
{
  var r : int;
  call p(5, out r);
};
#end

#guard accepted callOutMatchPgm

def callOutMismatchPgm : Program :=
#strata
program Core;
procedure p<a>(x : a, out y : a);
procedure Test()
{
  var r : bool;
  call p(5, out r);
};
#end

#guard !accepted callOutMismatchPgm

---------------------------------------------------------------------
-- Procedure definition
---------------------------------------------------------------------

def defMatchPgm : Program :=
#strata
program Core;
procedure p<a>(inout x : a, out y : a)
spec {
  ensures (y == x);
  ensures (old x == x);
};
#end

#guard accepted defMatchPgm

-- `y : a` cannot equal `MkBox(x) : Box a`.
def defOutMismatchPgm : Program :=
#strata
program Core;
datatype Box (a : Type) { MkBox(v : a) };
procedure p<a>(x : a, out y : a)
spec {
  ensures (y == MkBox(x));
};
#end

#guard !accepted defOutMismatchPgm

-- `x : a` cannot equal `MkBox(old x) : Box a`.
def defOldMismatchPgm : Program :=
#strata
program Core;
datatype Box (a : Type) { MkBox(v : a) };
procedure p<a>(inout x : a)
spec {
  ensures (x == MkBox(old x));
};
#end

#guard !accepted defOldMismatchPgm

end Strata.PolyProcConsistentInstTest

end
