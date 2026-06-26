/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Nondeterministic holes `<??>`

A nondeterministic hole `<??>` stands for an *arbitrary* value of the inferred
type. Unlike the deterministic hole `<?>` (which `EliminateDeterministicHoles`
replaces with a call to a fresh uninterpreted function, so repeated occurrences
agree), each `<??>` is havoced independently.

This file covers, end-to-end:
- Tautologies over a nondet value verify (the value is *some* value of its type).
- A specific-value assertion about a nondet value fails (it is *arbitrary*).
- Two distinct `<??>` need not agree.
- `<??>` is usable directly in a boolean position (`assert <??>`).
-/

/-! ### Tautologies over a nondet value hold -/

#eval testLaurel
#strata
program Laurel;
procedure nondetIntReflexive()
  opaque
{
  var x: int := <??>;
  assert x == x
};

procedure nondetBoolExcludedMiddle()
  opaque
{
  var b: bool := <??>;
  assert b || !b
};
#end

/-! ### A nondet value is arbitrary: specific-value assertions fail -/

#eval testLaurel <|
#strata
program Laurel;
procedure nondetIntIsArbitrary()
  opaque
{
  var x: int := <??>;
  assert x == 5
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#eval testLaurel <|
#strata
program Laurel;
procedure nondetBoolIsArbitrary()
  opaque
{
  var b: bool := <??>;
  assert b
//^^^^^^^^ error: assertion does not hold
};
#end

/-! ### Two distinct nondet holes need not agree -/

#eval testLaurel <|
#strata
program Laurel;
procedure nondetHolesAreIndependent()
  opaque
{
  var x: int := <??>;
  var y: int := <??>;
  assert x == y
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ### `<??>` directly in a boolean position is arbitrary -/

#eval testLaurel <|
#strata
program Laurel;
procedure nondetHoleInAssert()
  opaque
{
  assert <??>
//^^^^^^^^^^^ error: assertion does not hold
};
#end
