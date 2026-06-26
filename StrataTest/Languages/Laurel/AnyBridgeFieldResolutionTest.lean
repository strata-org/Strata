/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Regression tests for `Any`-typed field resolution: the cross-scope fallback in
`resolveFieldRef` fires only for `Any` targets, so a concrete target can't bind
an unrelated composite's field.
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## `meow` (on `Cat`) is not a field of `Dog`, so `d#meow` is rejected -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Dog { var bark: int }
composite Cat { var meow: int }
procedure test() opaque {
  var d: Dog := new Dog;
  var x: int := d#meow
//                ^^^^ error: Resolution failed: 'meow' is not defined
};
#end

/-! ## Correct field access on the same composites still resolves -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Dog { var bark: int }
composite Cat { var meow: int }
procedure test() opaque {
  var d: Dog := new Dog;
  var x: int := d#bark
};
#end

/-! ## An `Any`-typed target resolves a field cross-scope (gate TRUE branch) -/

#eval testLaurelResolution <|
#strata
program Laurel;
datatype Any { from_Reference(as_ref: int) }
composite Dog { var bark: int }
procedure test() opaque {
  var a: Any := from_Reference(0);
  var x: int := a#bark
};
#end

/-! ## An `Any`-typed target accessing a field defined on no composite still errors -/

#eval testLaurelResolution <|
#strata
program Laurel;
datatype Any { from_Reference(as_ref: int) }
composite Dog { var bark: int }
procedure test() opaque {
  var a: Any := from_Reference(0);
  var x: int := a#nope
//                ^^^^ error: Resolution failed: 'nope' is not defined
};
#end

/-! ## A field write/read round-trip verifies -/

#eval testLaurel <|
#strata
program Laurel;
composite Dog { var bark: int }
procedure test() opaque {
  var d: Dog := new Dog;
  d#bark := 7;
  assert d#bark == 7;
  d#bark := d#bark + 1;
  assert d#bark == 8
};
#end

/-! ## Two instances have independent fields (no aliasing collapse) -/

#eval testLaurel <|
#strata
program Laurel;
composite Dog { var bark: int }
procedure test() opaque {
  var d1: Dog := new Dog;
  var d2: Dog := new Dog;
  d1#bark := 1;
  d2#bark := 2;
  assert d1#bark == 1;
  assert d2#bark == 2
};
#end

/-! ## A false field assertion is caught by the verifier -/

#eval testLaurel <|
#strata
program Laurel;
composite Dog { var bark: int }
procedure test() opaque {
  var d: Dog := new Dog;
  d#bark := 1;
  assert d#bark == 2
//^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end
