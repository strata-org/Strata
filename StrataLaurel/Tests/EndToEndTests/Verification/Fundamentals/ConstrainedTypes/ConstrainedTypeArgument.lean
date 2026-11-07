/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Test: a datatype applied to a constrained type (`Option<nat>`) carries the
unfolded constraint `Option..isSome(o) ==> nat$constraint(Option..value(o))`.
Every read assumes it, so every write must check it: as a composite field, a
local, a procedure input and a procedure output.
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelVerification <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
datatype Option<T> { Nothing(), Some(value: T) }
composite Box { var opt: Option<nat> }

procedure fieldWriteInvalid(b: Box) opaque modifies b {
  b#opt := Some(-1);
//^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  var v: Option<nat> := b#opt;
  assert false
};

procedure fieldWriteValid(b: Box) opaque modifies b {
  b#opt := Some(1);
  var v: Option<nat> := b#opt;
  assert Option..isSome(v) ==> Option..value(v) >= 0
};

procedure fieldReadRecoversConstraint(b: Box) opaque {
  var v: Option<nat> := b#opt;
  assert Option..isSome(v) ==> Option..value(v) >= 0
};

procedure localWriteInvalid() opaque {
  var o: Option<nat> := Some(-1);
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  assert false
//^^^^^^^^^^^^ error: assertion does not hold
};

procedure localWriteValid() opaque {
  var o: Option<nat> := Some(1);
  o := Nothing();
  assert Option..isNothing(o)
};

procedure takesOption(o: Option<nat>) opaque
  ensures Option..isSome(o) ==> Option..value(o) >= 0
{
};

procedure inputInvalid() opaque {
  takesOption(Some(-1))
//^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
};

procedure inputValid() opaque {
  takesOption(Some(1))
};

procedure outputInvalid() returns (r: Option<nat>) opaque {
//                                    ^^^^^^^^^^^ error: postcondition could not be proved
  r := Some(-1)
//^^^^^^^^^^^^^ error: assertion could not be proved
};

procedure outputValid() returns (r: Option<nat>) opaque {
  r := Some(1)
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
datatype A<T> { MkA(t: T, b: B<T>), NilA() }
datatype B<T> { MkB(a: A<T>) }
procedure f(a: A<int>) opaque { assert true };
procedure g(a: A<int>) opaque {
  assert false
//^^^^^^^^^^^^ error: assertion does not hold
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
constrained int32 = x: int where x >= -2147483648 && x <= 2147483647 witness 0
datatype Entry<V> { MkEntry(key: int32, value: V) }
datatype Holder { MkHolder(e: Entry<bool>) }
procedure takesEntry(e: Entry<bool>) opaque;
procedure ownFieldNotEnforced(h: Holder) opaque {
  var e: Entry<bool> := Holder..e!(h);
  takesEntry(Holder..e!(h));
  var big: Entry<nat> := MkEntry(2147483649, 1);
  assert true
};
procedure typeArgFieldEnforced() opaque {
  var e: Entry<nat> := MkEntry(0, -1);
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
  assert true
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
datatype Option<T> { Nothing(), Some(value: T) }
procedure holePlain() opaque {
  var n: nat := <??>;
  assert n >= 0
};
procedure holeApplied() opaque {
  var o: Option<nat> := <??>;
  assert Option..isSome(o) ==> Option..value(o) >= 0
};
#end
