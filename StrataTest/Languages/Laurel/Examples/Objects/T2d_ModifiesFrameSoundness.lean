/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Soundness of the quantifier-free modifies frame under `--use-array-theory`: illegal
writes are rejected, legal shapes verify, callers may assume the free frame, and a
fresh object exposed to a caller is not pinned by it.
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

private def arrayTheoryOpts :=
  { defaultLaurelTestOptions with
    translateOptions := { defaultLaurelTestOptions.translateOptions with enumeratedModifiesClauses := true },
    verifyOptions := { defaultLaurelTestOptions.verifyOptions with useArrayTheory := true } }

/-! ## 1. Illegal writes are rejected -/

#eval testLaurel (options := arrayTheoryOpts) <|
#strata
program Laurel;
composite Container {
  var value: int
}

procedure writeNonFrameConditional(c: Container, d: Container)
//        ^^^^^^^^^^^^^^^^^^^^^^^^ error: modifies clause does not hold
  opaque
  modifies d
{
  if d#value > 0 then {
    c#value := 7
  }
};

procedure writeAfterEarlyReturn(c: Container, d: Container) returns (b: bool)
//        ^^^^^^^^^^^^^^^^^^^^^ error: modifies clause does not hold
  opaque
  modifies d
{
  if d#value > 100 then {
    return true
  };
  c#value := 7;
  return false
};

procedure writeOneOfManyNonFrame(c: Container, d: Container, e: Container)
//        ^^^^^^^^^^^^^^^^^^^^^^ error: modifies clause does not hold
  opaque
  modifies c
  modifies d
{
  e#value := 9
};

procedure writeFrameAndNonFrame(c: Container, d: Container)
//        ^^^^^^^^^^^^^^^^^^^^^ error: modifies clause does not hold
  opaque
  modifies c
{
  c#value := 1;
  d#value := 2
};

procedure writeNestedIf(c: Container, d: Container)
//        ^^^^^^^^^^^^^ error: modifies clause does not hold
  opaque
  modifies d
{
  if d#value > 0 then {
    if d#value > 5 then {
      c#value := 1
    }
  }
};
#end

/-! ## 2. Legal shapes still verify -/

#eval testLaurel (options := arrayTheoryOpts) <|
#strata
program Laurel;
composite Container {
  var value: int
}

procedure writeFrameConditional(c: Container)
  opaque
  modifies c
{
  if c#value > 0 then {
    c#value := c#value + 1
  }
};

procedure modifyThenEarlyReturn(c: Container) returns (b: bool)
  opaque
  modifies c
{
  c#value := 1;
  if c#value > 0 then {
    return true
  };
  return false
};

procedure modifyTwoDeclared(c: Container, d: Container)
  opaque
  modifies c
  modifies d
{
  c#value := 1;
  d#value := 2
};

procedure allocThenModifyDeclared(c: Container)
  opaque
  modifies c
{
  var t: Container := new Container;
  t#value := 99;
  c#value := 5
};
#end

/-! ## 3. Callers may assume the free frame; it does not over-promise -/

#eval testLaurel (options := arrayTheoryOpts) <|
#strata
program Laurel;
composite Container {
  var value: int
}

procedure bodyModifier(c: Container) returns (b: bool)
  opaque
  modifies c
{
  c#value := c#value + 1;
  true
};

procedure allocatingBody(c: Container) returns (b: bool)
  opaque
  modifies c
{
  c#value := c#value + 1;
  var t: Container := new Container;
  t#value := 99;
  true
};

procedure bodyModifierTwo(c: Container, d: Container)
  opaque
  modifies c
  modifies d
{
  c#value := 1;
  d#value := 2
};

procedure callerUnrelatedPreserved()
  opaque
{
  var c: Container := new Container;
  var d: Container := new Container;
  var x: int := d#value;
  var b: bool := bodyModifier(c);
  assert x == d#value
};

procedure callerModifiedNotPreserved()
  opaque
{
  var c: Container := new Container;
  var x: int := c#value;
  var b: bool := bodyModifier(c);
  assert x == c#value
//^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};

procedure callerExactValuePreserved()
  opaque
{
  var c: Container := new Container;
  var d: Container := new Container;
  d#value := 5;
  var b: bool := bodyModifier(c);
  assert d#value == 5
};

procedure callerOfAllocatingBody()
  opaque
{
  var c: Container := new Container;
  var d: Container := new Container;
  var x: int := d#value;
  var b: bool := allocatingBody(c);
  assert x == d#value
};

procedure callerMultiUnrelated()
  opaque
{
  var c: Container := new Container;
  var d: Container := new Container;
  var e: Container := new Container;
  var x: int := e#value;
  bodyModifierTwo(c, d);
  assert x == e#value
};
#end

/-! ## 4. Multiple exits and bodiless/body parity -/

#eval testLaurel (options := arrayTheoryOpts) <|
#strata
program Laurel;
composite Container {
  var value: int
}

procedure multiExitAllLegal(c: Container) returns (b: bool)
  opaque
  modifies c
{
  c#value := 1;
  if c#value > 0 then {
    c#value := 2;
    return true
  };
  c#value := 3;
  return false
};

procedure illegalAfterLegalEarlyExit(c: Container, d: Container) returns (b: bool)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^ error: modifies clause does not hold
  opaque
  modifies c
{
  if c#value > 0 then {
    c#value := 1;
    return true
  };
  d#value := 9;
  return false
};

procedure bodilessModifier(c: Container)
  opaque
  modifies c;

procedure callerOfBodiless()
  opaque
{
  var c: Container := new Container;
  var d: Container := new Container;
  var x: int := d#value;
  bodilessModifier(c);
  assert x == d#value
};
#end

/-! ## 5. A fresh object exposed to a caller is not pinned by the frame -/

#eval testLaurel (options := arrayTheoryOpts) <|
#strata
program Laurel;
composite Container {
  var value: int
  var child: Container
}

procedure stashFresh(c: Container)
  opaque
  modifies c
{
  var t: Container := new Container;
  t#value := 42;
  c#child := t
};

procedure callerCannotPinFreshField()
  opaque
{
  var c: Container := new Container;
  stashFresh(c);
  assert c#child#value == 42
//^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end
