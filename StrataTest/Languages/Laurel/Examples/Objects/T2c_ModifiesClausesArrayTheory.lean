/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Under `--use-array-theory`, the `ModifiesClauses` pass emits a quantifier-free
heap-equation frame —
  `data!($heap) == update(data!(old), ref, select(data!($heap), ref))`
— instead of the `forall obj fld. notModified(obj) ==> readField(old) == readField(new)`
form. The same procedures must verify under either encoding; this pins the
array-theory path. Mirrors `T2_ModifiesClauses` but with `useArrayTheory := true`.
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurel
    (options := { defaultLaurelTestOptions with
      translateOptions := { defaultLaurelTestOptions.translateOptions with useArrayTheory := true },
      verifyOptions := { defaultLaurelTestOptions.verifyOptions with useArrayTheory := true } }) <|
#strata
program Laurel;
composite Container {
  var value: int
}

procedure modifyContainerOpaque(c: Container) returns (b: bool)
  opaque
  modifies c
{
  c#value := c#value + 1;
  true
};

procedure caller()
  opaque
{
  var c: Container := new Container;
  var d: Container := new Container;
  var x: int := d#value;
  var b: bool := modifyContainerOpaque(c);
  assert x == d#value // pass: d#value is preserved (d ∉ modifies)
};

procedure multipleModifiesClauses(c: Container, d: Container, e: Container)
  opaque
  modifies c
  modifies d
;

procedure multipleModifiesClausesCaller()
  opaque
{
  var c: Container := new Container;
  var d: Container := new Container;
  var e: Container := new Container;
  var x: int := e#value;
  multipleModifiesClauses(c, d, e);
  assert x == e#value // pass: e is preserved (not in the modifies set)
};

procedure newObjectDoNotCountForModifies()
  opaque
{
  var c: Container := new Container;
  c#value := 1
};

// Regression: an allocating body verifies under array theory (bodies use the pointwise frame).
procedure allocatesInModifiesBody(c: Container) returns (b: bool)
  opaque
  modifies c
{
  c#value := c#value + 1;
  var t: Container := new Container;
  t#value := 99;
  true
};

// Regression: a body that allocates via a CALL still verifies (the callee
// newObjectDoNotCountForModifies grows the heap); the pointwise frame tolerates it.
procedure allocatesViaCall(c: Container) returns (b: bool)
  opaque
  modifies c
{
  c#value := c#value + 1;
  newObjectDoNotCountForModifies();
  true
};

// Soundness: writes outside the modifies clause are still rejected.

procedure modifyContainerWithoutPermission2(c: Container, d: Container)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: modifies clause does not hold
  opaque
  modifies d
{
    c#value := 2
};

procedure modifyContainerWithoutPermission3(c: Container, d: Container)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: modifies clause could not be proved
  opaque
  modifies d
{
    var i: bool := modifyContainerOpaque(c)
};
#end
