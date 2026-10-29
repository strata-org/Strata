/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
/-
Soundness of the quantifier-free modifies frame under `--use-array-theory`: illegal
writes are rejected, legal shapes verify, callers may assume the free frame, a
fresh object exposed to a caller is not pinned by it, and a procedure that may
allocate does not expose it.
-/

meta import StrataLaurel.Tests.Util.TestLaurel
import StrataLaurel.Implementation.LaurelPass
import StrataLaurel.Implementation.LaurelToCoreSchemaPass

open StrataTest.Util
open Strata

private meta def arrayTheoryOpts :=
  { defaultLaurelTestOptions with
    translateOptions := { defaultLaurelTestOptions.translateOptions with enumeratedModifiesClauses := true },
    verifyOptions := { defaultLaurelTestOptions.verifyOptions with useArrayTheory := true } }

/-! ## 1. Illegal writes are rejected -/

#eval testLaurelVerification (options := arrayTheoryOpts) <|
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

#eval testLaurelVerification (options := arrayTheoryOpts) <|
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

#eval testLaurelVerification (options := arrayTheoryOpts) <|
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
//^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
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

#eval testLaurelVerification (options := arrayTheoryOpts) <|
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

#eval testLaurelVerification (options := arrayTheoryOpts) <|
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

/-! ## 6. A procedure that may allocate keeps the quantified frame

The enumerated frame says that every row the clause does not name is unchanged, also the
rows of the objects the call creates. A caller observes such a row through `old` or a
quantified precondition. Without the quantified frame, each `assert false` below verifies,
and so does the `assert t#value == 0` after the overridden call, which fails at run time
when `p` is a `FreshPicker`. -/

#eval testLaurelVerification (options := arrayTheoryOpts) <|
#strata
program Laurel;
composite Container {
  var value: int
}

procedure bumpFresh(c: Container) returns (t: Container)
  opaque
  ensures t#value == old(t#value) + 1
  ensures t != c
  modifies c
{
  var u: Container := new Container;
  u#value := u#value + 1;
  return u
};

procedure callerOfBumpFresh(c: Container)
  opaque
  modifies c
{
  var t: Container := bumpFresh(c);
  assert false
//^^^^^^^^^^^^ error: assertion could not be proved
};

procedure makeFresh(c: Container) returns (t: Container)
  opaque
  ensures t#value == 1
  ensures t != c
  modifies c
{
  var u: Container := new Container;
  u#value := 1;
  return u
};

procedure callerOfMakeFresh(c: Container)
  requires forall(o: Container) => o#value == 0
  opaque
  modifies c
{
  var t: Container := makeFresh(c);
  assert false
//^^^^^^^^^^^^ error: assertion could not be proved
};

procedure makeFreshIndirectly(c: Container) returns (t: Container)
  opaque
  ensures t#value == 1
  ensures t != c
  modifies c
{
  var u: Container := makeFresh(c);
  return u
};

procedure callerOfMakeFreshIndirectly(c: Container)
  requires forall(o: Container) => o#value == 0
  opaque
  modifies c
{
  var t: Container := makeFreshIndirectly(c);
  assert false
//^^^^^^^^^^^^ error: assertion could not be proved
};

procedure makeFreshBodiless(c: Container) returns (t: Container)
  opaque
  ensures t#value == 1
  ensures t != c
  modifies c;

procedure callerOfMakeFreshBodiless(c: Container)
  requires forall(o: Container) => o#value == 0
  opaque
  modifies c
{
  var t: Container := makeFreshBodiless(c);
  assert false
//^^^^^^^^^^^^ error: assertion could not be proved
};

procedure bump(c: Container)
  opaque
  modifies c
{
  c#value := c#value + 1
};

// A procedure that cannot allocate keeps the enumerated frame, which also covers the
// rows of objects allocated after the call.
procedure callerOfBump(c: Container)
  requires forall(o: Container) => o#value == 0
  opaque
  modifies c
{
  bump(c);
  var t: Container := new Container;
  assert t#value == 0
};
#end

#eval testLaurelVerification (options := arrayTheoryOpts) <|
#strata
program Laurel;
composite Container {
  var value: int
}
composite Picker {
  var kept: Container
  procedure pick(self: Picker, c: Container) returns (t: Container)
    requires self#kept != c
    opaque
    ensures t != c
    modifies c
  {
    return self#kept
  };
}
composite FreshPicker extends Picker {
  procedure pick(self: FreshPicker, c: Container) returns (t: Container)
    requires self#kept != c
    opaque
    ensures t != c
    modifies c
  {
    var u: Container := new Container;
    u#value := 1;
    return u
  };
}

procedure callerOfPick(p: Picker, c: Container)
  requires forall(o: Container) => o#value == 0
  requires p#kept != c
  opaque
  modifies c
{
  var t: Container := p#pick(c);
  assert t#value == 0
//^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

/-! A function called under `old`, and a datatype argument, reach the fresh object's
pre-state row without a field read written under `old`. -/

#eval testLaurelVerification (options := arrayTheoryOpts) <|
#strata
program Laurel;
composite Container {
  var value: int
}
datatype Pair { MkPair(c: Container, i: int) }

procedure getValue(c: Container): int { return c#value };

procedure getPairValue(p: Pair): int { return Pair..c!(p)#value };

procedure bumpViaGetter(c: Container) returns (t: Container)
  opaque
  ensures getValue(t) == old(getValue(t)) + 1
  ensures t != c
  modifies c
{
  var u: Container := new Container;
  u#value := u#value + 1;
  return u
};

procedure callerOfBumpViaGetter(c: Container)
  opaque
  modifies c
{
  var t: Container := bumpViaGetter(c);
  assert false
//^^^^^^^^^^^^ error: assertion could not be proved
};

procedure bumpViaDatatype(c: Container) returns (t: Container)
  opaque
  ensures getPairValue(MkPair(t, 1)) == old(getPairValue(MkPair(t, 1))) + 1
  ensures t != c
  modifies c
{
  var u: Container := new Container;
  u#value := u#value + 1;
  return u
};

procedure callerOfBumpViaDatatype(c: Container)
  opaque
  modifies c
{
  var t: Container := bumpViaDatatype(c);
  assert false
//^^^^^^^^^^^^ error: assertion could not be proved
};
#end
