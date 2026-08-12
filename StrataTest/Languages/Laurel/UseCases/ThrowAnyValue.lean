/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Modeling JavaScript's "throw *any* value" with the current exception feature set.

A *use case* rather than a semantics test (hence `UseCases/`, see the test README):
it claims that the pattern a JS front end needs is expressible and reads reasonably,
not that a particular construct behaves a particular way. The rules for `throw` itself
— including that a bare primitive is a legal operand, since Laurel imposes no root
exception type — are in `EndToEndTests/Execution/Exceptions/Throw.lean`.

JS lets you `throw` an arbitrary value (`throw 42`, `throw "boom"`, an object, …). A
JS-to-Laurel front end models this by *boxing*: it wraps the thrown value in a single
carrier composite and unwraps it in the handler. Boxing gives every thrown value one
composite type, so `catch`/`is` dispatch and the `Result` lowering work uniformly and
the caught binding is typed at that single carrier.

Boxing is what a front end needs when the *same* `try` can see values of unrelated
kinds. It is not what a single primitive throw requires — that case needs no carrier
at all, and is covered in `Throw.lean`.

Run through `testLaurel` (the verifier) rather than `testLaurelMultiple`: the carrier
is a composite, so these allocate on the heap, and the interpret path does not support
the heap yet.
-/

-- `throw 42` — a number (not an Error) is boxed, caught, and unwrapped.
#eval testLaurel <|
#strata
program Laurel;
datatype JsValue {
  JsNum(num: int),
  JsStr(str: string)
}
composite AnyThrown {
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
composite AnyThrown {
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
composite AnyThrown {
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
