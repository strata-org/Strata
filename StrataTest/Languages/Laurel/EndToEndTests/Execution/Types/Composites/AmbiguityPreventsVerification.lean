/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel
open StrataTest.Util
open Strata

/-! CONTROL: a FALSE assertion with NO ambiguity verifies and FAILS -- the assert
    is actually checked when the program is not discarded. -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Base {
  procedure m(self: Base) returns (r: int)
    opaque ensures r == 4 { return 4 };
}
composite Only extends Base { }
procedure go(o: Only)
  opaque
{
  var x: int := o#m();
  assert x == 999
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! SOUNDNESS: SAME false assertion, but the call is now AMBIGUOUS. If the ambiguity
    error prevents verification (program discarded), the assertion is NEVER checked,
    so only the ambiguity error fires. A false \"assert x == 999\" that produced no
    assertion failure here would otherwise be a silent unsound pass. -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite L {
  procedure m(self: L) returns (r: int)
    opaque ensures r == 1 { return 1 };
}
composite R {
  procedure m(self: R) returns (r: int)
    opaque ensures r == 2 { return 2 };
}
composite D extends L, R { }
procedure go(d: D)
  opaque
{
  var x: int := d#m();
//              ^^^^^ error: call to 'm' is ambiguous: 'D' inherits it from the unrelated types L, R
  assert x == 999
};
#end
