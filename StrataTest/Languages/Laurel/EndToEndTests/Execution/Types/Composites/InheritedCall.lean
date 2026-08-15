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
    SUBTYPE contract (r == 5) binds, not the ancestor one. C3's override must
    REFINE B3's contract (Liskov behavioral subtyping): `r == 5` refines the
    weaker `r >= 0`, so the override is accepted and its own contract binds. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite B3 {
  procedure m(self: B3) returns (r: int)
    opaque
    ensures r >= 0
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

/-! ## 4. Upcast + override: through a B4-typed variable holding a C4, the call
    DYNAMICALLY DISPATCHES to C4's override (r == 5), not B4$m. The override is sound:
    C4.m `ensures r == 5` refines B4.m's weaker `ensures r >= 0` (Liskov), so B4's
    static contract still holds at the call site while the derived body runs. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite B4 {
  procedure m(self: B4) returns (r: int)
    opaque
    ensures r >= 0
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
procedure go()
  opaque
{
  var b: B4 := new C4;
  var x: int := b#m();
  assert x == 5
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

/-! ## 6. Dispatcher fallthrough: a B6-typed variable holding an ACTUAL B6 (not
    any overrider) runs the dispatcher's fallthrough branch — B6's own `$impl`.
    Contracts are made DISCRIMINATING so the branch is pinned, not just "some
    non-negative value": B6.m guarantees `r <= 100` (fallthrough post) and the C6 override
    guarantees the stronger `r == 50` (which refines it: 50 <= 100). For a
    `new B6` only the fallthrough (owner) post is exposed, so `assert x <= 100`
    verifies but the child's `x == 50` does not (twin 6b). Every
    other dispatch case holds a derived instance and takes an overrider branch;
    this is the one exercising the fallthrough + the guarded owner post. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite B6 {
  procedure m(self: B6) returns (r: int)
    opaque
    ensures r <= 100
  {
    return 4
  };
}
composite C6 extends B6 {
  procedure m(self: C6) returns (r: int)
    opaque
    ensures r == 50
  {
    return 50
  };
}
procedure go()
  opaque
{
  var b: B6 := new B6;
  var x: int := b#m();
  assert x <= 100
};
#end

/-! ## 6b. Fallthrough must-fail twin: for a genuine `new B6`, the dispatcher
    exposes ONLY the guarded owner post (`r <= 100`), NOT the C6b override's
    stronger `r == 50` — so asserting the child's guarantee must FAIL. Pins that the
    fallthrough is non-vacuous (it does not leak the override's stronger post to
    a base-typed receiver) — the runtime-tag discrimination is real. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite B6b {
  procedure m(self: B6b) returns (r: int)
    opaque
    ensures r <= 100
  {
    return 4
  };
}
composite C6b extends B6b {
  procedure m(self: C6b) returns (r: int)
    opaque
    ensures r == 50
  {
    return 50
  };
}
procedure go()
  opaque
{
  var b: B6b := new B6b;
  var x: int := b#m();
  assert x == 50
//^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

/-! ## 7. Three-level dispatch: a GP7-typed variable holding a C7 (two hops down)
    dispatches to C7's override (r == 6), through the middle P7. Pins that the
    most-derived overrider wins across a multi-level chain, not the nearest
    declared ancestor. Each override refines its parent (6 ⊢ r>=1 ⊢ r>=0). -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite GP7 {
  procedure m(self: GP7) returns (r: int)
    opaque
    ensures r >= 0
  {
    return 1
  };
}
composite P7 extends GP7 {
  procedure m(self: P7) returns (r: int)
    opaque
    ensures r >= 1
  {
    return 2
  };
}
composite C7 extends P7 {
  procedure m(self: C7) returns (r: int)
    opaque
    ensures r == 6
  {
    return 6
  };
}
procedure go()
  opaque
{
  var g: GP7 := new C7;
  var x: int := g#m();
  assert x == 6
};
#end

/-! ## 8. Sibling dispatch: two independent overriders of the same base. A
    B8-typed variable holding a C8b runs C8b's override (r == 7), NOT the sibling
    C8a's (r == 6) nor the base's — the runtime tag selects the correct branch. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite B8 {
  procedure m(self: B8) returns (r: int)
    opaque
    ensures r >= 0
  {
    return 4
  };
}
composite C8a extends B8 {
  procedure m(self: C8a) returns (r: int)
    opaque
    ensures r == 6
  {
    return 6
  };
}
composite C8b extends B8 {
  procedure m(self: C8b) returns (r: int)
    opaque
    ensures r == 7
  {
    return 7
  };
}
procedure go()
  opaque
{
  var b: B8 := new C8b;
  var x: int := b#m();
  assert x == 7
};
#end
