/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Modeling JavaScript-style "throw *any* value" on top of the `BaseException`-rooted
channel.

Laurel requires a thrown value to be a subtype of `BaseException`, but JS lets you
`throw` an arbitrary value (`throw 42`, `throw "boom"`, an object, …). A JS→Laurel
front-end bridges the two by *boxing*: it wraps the thrown value in a single
carrier composite that extends `BaseException`, and unwraps it in the handler.

    // JS
    throw v;
    try { … } catch (x) { … x … }

    // desugared to Laurel
    var t: AnyThrown := new AnyThrown; t#value := v; throw t;
    try { … } catch e when e is AnyThrown { var x := (e as AnyThrown)#value; … x … }

The arbitrary payload is a `JsValue` tagged union — the same "any value"
representation a JS front-end needs anyway. The exceptional channel, `Result`
lowering, and `catch`/`is` dispatch are all unchanged; the arbitrariness lives in
the box's field, not in the thrown type.

Note: `JsValue` here has just `JsNum`/`JsStr` to keep the example small. JS's
value space is a fixed, finite set of kinds, so this datatype can be extended as
needed with further constructors — `JsBool`, `JsUndefined`, `JsNull`,
`JsObj(ref: …)` for objects/Errors, etc. — to represent any JS value.
-/

-- `throw 42` — a number (not an Error) is boxed, caught, and unwrapped.
#eval testLaurel <|
#strata
program Laurel;
datatype JsValue {
  JsNum(num: int),
  JsStr(str: string)
}
composite AnyThrown extends BaseException {
  value: JsValue
}
procedure jsThrowNumber()
  returns (r: int)
  opaque
  ensures r == 42
{
  r := 0;
  var t: AnyThrown := new AnyThrown;
  t#value := JsNum(42);
  try {
    throw t
  } catch e when e is AnyThrown {
    var v: JsValue := (e as AnyThrown)#value;
    assert JsValue..isJsNum(v);
    r := JsValue..num(v)
  }
};
#end

-- `throw "boom"` — a string value is boxed and caught; the handler observes it
-- is a `JsStr`.
#eval testLaurel <|
#strata
program Laurel;
datatype JsValue {
  JsNum(num: int),
  JsStr(str: string)
}
composite AnyThrown extends BaseException {
  value: JsValue
}
procedure jsThrowString()
  returns (r: bool)
  opaque
  ensures r
{
  r := false;
  var t: AnyThrown := new AnyThrown;
  t#value := JsStr("boom");
  try {
    throw t
  } catch e when e is AnyThrown {
    var v: JsValue := (e as AnyThrown)#value;
    r := JsValue..isJsStr(v)
  }
};
#end

-- Negative: the boxed payload's kind is tracked — a string value is not a
-- number, so asserting `isJsNum` in the handler cannot be proved.
#eval testLaurel <|
#strata
program Laurel;
datatype JsValue {
  JsNum(num: int),
  JsStr(str: string)
}
composite AnyThrown extends BaseException {
  value: JsValue
}
procedure jsThrowStringBad()
  opaque
{
  var t: AnyThrown := new AnyThrown;
  t#value := JsStr("boom");
  try {
    throw t
  } catch e when e is AnyThrown {
    var v: JsValue := (e as AnyThrown)#value;
    assert JsValue..isJsNum(v)
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  }
};
#end
