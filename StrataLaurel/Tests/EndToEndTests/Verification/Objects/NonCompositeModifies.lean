/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
/-
Regression test for issue #490: a modifies clause referencing a non-composite
type (e.g. a parameter of type int) previously caused an infinite loop
in laurelAnalyze. The fix filters out non-composite modifies entries and emits
a diagnostic error.
-/

meta import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelVerification <|
#strata
program Laurel;
composite Container {
  var value: int
}

procedure incWithPrimitiveModifies(x: int) returns (r: int)
  opaque
  modifies x
//         ^ error: modifies clause entry has non-composite type 'int'; only a heap object can be framed
{
  r := x + 1
};

procedure modifyContainerAndPrimitive(c: Container, x: int)
  opaque
  modifies c
  modifies x
//         ^ error: modifies clause entry has non-composite type 'int'; only a heap object can be framed
{
  c#value := 1
};
#end

/-! Value types are rejected regardless of shape: bare (`Color`, `Token`) and applied
(`Box<int>`, `Sequence<int>`), datatype and opaque alike. `GHolder<int>` is the positive
control — a generic-composite instantiation shares the `.Applied` shape but must survive. -/

#eval testLaurelVerification <|
#strata
program Laurel;
opaque Token
datatype Color { Red() , Green() }
datatype Box<T> { Wrap(x: T) }
composite Holder {
  var v: int
}
composite GHolder<T> {
  var w: T
}

procedure nominalValueModifies(s: Sequence<int>, t: Token, c: Color, b: Box<int>,
                               h: Holder, g: GHolder<int>)
  opaque
  modifies s
//         ^ error: modifies clause entry has non-composite type 'Sequence<int>'; only a heap object can be framed
  modifies t
//         ^ error: modifies clause entry has non-composite type 'Token'; only a heap object can be framed
  modifies c
//         ^ error: modifies clause entry has non-composite type 'Color'; only a heap object can be framed
  modifies b
//         ^ error: modifies clause entry has non-composite type 'Box<int>'; only a heap object can be framed
  modifies h
  modifies g
{
  h#v := 1;
  g#w := 2
};
#end

/-! A FIELD target `o#f` gates on the OWNER's type, so a value-type owner is dropped.
`Box<int>` reaches the field arm as an `.Applied` owner, and reports twice: fields exist only on
composites, so a value-type owner fails field resolution as well. -/

#eval testLaurelVerification <|
#strata
program Laurel;
datatype Box<T> { Wrap(x: T) }
composite Holder {
  var v: int
}

procedure fieldTargetOnValueOwner(b: Box<int>, h: Holder)
  opaque
  modifies b#x
//           ^ error: Resolution failed: 'x' is not defined
//           ^ error: modifies clause field target has non-composite owner type 'Box<int>'; only a heap object can be framed
  modifies h
{
  h#v := 1
};
#end

/-! A target whose type failed to resolve is dropped SILENTLY. Resolution has already reported
the real error, and restating it as "non-composite" would only bury it. `Sequence<NoSuchType>`
covers the nested case, where the head resolves and only an argument did not. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Holder {
  var v: int
}

procedure unresolvedModifies(q: NoSuchType, n: Sequence<NoSuchType>, h: Holder)
//                              ^^^^^^^^^^ error: Resolution failed: 'NoSuchType' is not defined
//                                                      ^^^^^^^^^^ error: Resolution failed: 'NoSuchType' is not defined
  opaque
  modifies q
  modifies n
  modifies h
{
  h#v := 1
};
#end

/-! An EXCEPTIONAL frame (`throwsOn C { modifies … }`) is gated exactly like a normal one, and
reports at resolution. Without this, an unframeable target survives to `EliminateExceptions`,
which re-resolves the frame and reports the gate's own message as a compiler bug. `c` inside the
case is the positive control — the gate must still accept a composite there. -/

#eval testLaurelVerification <|
#strata
program Laurel;
opaque Token
composite Cell {
  var value: int
}
composite Err {}

procedure exceptionalFrame(c: Cell, t: Token, fail: bool)
  throws (e: Err)
  opaque
  modifies c
  throwsOn fail {
    modifies c
    modifies t
//           ^ error: modifies clause entry has non-composite type 'Token'; only a heap object can be framed
  }
{
  if fail then {
    var e: Err := new Err;
    throw e
  };
  c#value := 42
};
#end

/-! Same for a type resolution REFUSED rather than failed to find: a bare reference to a generic
nominal type is not a usable type, so it collapses to `Unknown` and the modifies entry goes
quietly. Only the arity error, which says what to fix, is reported. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Holder {
  var v: int
}

procedure bareGenericModifies(s: Set, h: Holder)
//                               ^^^ error: generic opaque type 'Set' must be applied to 1 type argument(s)
  opaque
  modifies s
  modifies h
{
  h#v := 1
};
#end
