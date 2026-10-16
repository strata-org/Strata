/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.Tests.Util.TestLaurel

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

-- No Core interpreter: "<??>" does not reduce in the Core interpreter ("condition did not reduce to bool").
#eval testLaurelExecution { skipCoreInterpreter := true } <|
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

procedure runAll() entry opaque {
  nondetIntReflexive();
  nondetBoolExcludedMiddle()
};
#end

/-! ### A nondet value is arbitrary: specific-value assertions fail -/

-- No Core interpreter: "<??>" does not reduce in the Core interpreter ("condition did not reduce to bool").
#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
procedure nondetIntIsArbitrary()
  opaque
{
  var x: int := <??>;
  assert x == 5
//^^^^^^^^^^^^^ error: assertion does not hold
};

procedure runAll() entry opaque {
  nondetIntIsArbitrary()
};
#end

-- No Core interpreter: "<??>" does not reduce in the Core interpreter ("condition did not reduce to bool").
#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
procedure nondetBoolIsArbitrary()
  opaque
{
  var b: bool := <??>;
  assert b
//^^^^^^^^ error: assertion does not hold
};

procedure runAll() entry opaque {
  nondetBoolIsArbitrary()
};
#end

/-! ### Two distinct nondet holes need not agree -/

-- No interpreters: "<??>" does not reduce in the Core interpreter ("condition did not reduce to bool"); the Laurel interpreter gives both holes the default 0, so the assert holds.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
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

-- No Core interpreter: "<??>" does not reduce in the Core interpreter ("condition did not reduce to bool").
#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
procedure nondetHoleInAssert()
  opaque
{
  assert <??>
//^^^^^^^^^^^ error: assertion does not hold
};

procedure runAll() entry opaque {
  nondetHoleInAssert()
};
#end
