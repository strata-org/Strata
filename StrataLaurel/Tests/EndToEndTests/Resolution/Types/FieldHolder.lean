/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # A field resolves in its holder's composite, not another

Not in a composite named like the holder's type variable or an alias's parameter, and, in a method,
not in the enclosing composite, whether the holder is an `int` or a hole. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite T { var x: int }

procedure typeVariableNamedLikeComposite<T>(t: T) returns (r: int)
  opaque
{
  r := t#x
//       ^ error: Resolution failed: 'x' is not defined
};

type Id<T> = T
procedure aliasParameterNamedLikeComposite(t: Id<int>) returns (r: int)
  opaque
{
  r := t#x
//       ^ error: Resolution failed: 'x' is not defined
};

composite C {
  var x: int
  procedure intInMethod(self: C, z: int) returns (r: int)
    opaque
  {
    r := z#x
//         ^ error: Resolution failed: 'x' is not defined
  };
  procedure holeInMethod(self: C) returns (r: int)
    opaque
  {
    r := <?>#x
//           ^ error: Resolution failed: 'x' is not defined
  };
}
#end

/-! In a method of a composite whose own type is gradual, a missing field is still reported. -/

#eval testLaurelResolution (gradualTypes := ({} : Std.HashSet String).insert "C") <|
#strata
program Laurel;
composite C {
  var x: int
  procedure inGradualComposite(self: C, z: int) returns (r: int)
    opaque
  {
    r := z#y
//         ^ error: Resolution failed: 'y' is not defined
  };
}
#end
