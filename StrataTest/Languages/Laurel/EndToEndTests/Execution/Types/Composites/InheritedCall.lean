/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/- Inherited instance-procedure calls: c#m() resolves when m is declared on an
   ancestor composite, by walking the receiver type's extends chain to the
   declaring type's key (B$m). -/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite B {
  procedure m(self: B) returns (r: int)
    opaque
    ensures r == 4
  {
    return 4
  };
}
composite C extends B { }
procedure go(c: C)
  opaque
{
  var x: int := c#m();
  assert x == 4
};
#end

/-! ## 2. Deep chain: the method is two extends hops away. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite A2 {
  procedure m(self: A2) returns (r: int)
    opaque
    ensures r == 4
  {
    return 4
  };
}
composite B2 extends A2 { }
composite C2 extends B2 { }
procedure go(c: C2)
  opaque
{
  var x: int := c#m();
  assert x == 4
};
#end

/-! ## 3. Override: the receiver type re-declares m — nearest wins, so the
    SUBTYPE contract (r == 5) binds, not the ancestor one. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite B3 {
  procedure m(self: B3) returns (r: int)
    opaque
    ensures r == 4
  {
    return 4
  };
}
composite C3 extends B3 {
  procedure m(self: C3) returns (r: int)
    opaque
    ensures r == 5
  {
    return 5
  };
}
procedure go(c: C3)
  opaque
{
  var x: int := c#m();
  assert x == 5
};
#end

/-! ## 4. Upcast + override: through a B4-typed variable the STATIC type
    selects B4$m (r == 4) — resolution is static, not dynamic dispatch. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite B4 {
  procedure m(self: B4) returns (r: int)
    opaque
    ensures r == 4
  {
    return 4
  };
}
composite C4 extends B4 {
  procedure m(self: C4) returns (r: int)
    opaque
    ensures r == 5
  {
    return 5
  };
}
procedure go(c: C4)
  opaque
{
  var b: B4 := c;
  var x: int := b#m();
  assert x == 4
};
#end

/-! ## 5. Negative: no type in the chain declares the method — the diagnostic
    still names the RECEIVER type (C5$missing), not an ancestor. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite B5 { }
composite C5 extends B5 { }
procedure go(c: C5)
  opaque
{
  var x: int := c#missing();
//              ^^^^^^^^^^^ error: Resolution failed: 'C5$missing' is not defined
  assert x == 4
};
#end
