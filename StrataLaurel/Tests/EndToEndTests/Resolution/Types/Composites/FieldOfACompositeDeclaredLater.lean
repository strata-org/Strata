/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # A field access does not depend on the order the composites are declared in -/

/-! ## A later composite's field that shares its name with a field of the accessing composite

`b#v` is `B`'s `int` field, not `A`'s `bool` one. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite A { var v: bool
  procedure m(self: A, b: B) opaque modifies b { b#v := 1 };
}
composite B { var v: int }
#end

/-! ## A field inherited from a parent declared after the child -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Sub extends Base { var own: int }
composite Base { var k: int }
procedure p(s: Sub) opaque modifies s { s#k := 1 };
#end
