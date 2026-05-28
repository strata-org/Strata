/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the resolution pass detects duplicate names in the same scope.
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Duplicate static procedure names -/

#eval testLaurelExpectResolution <|
#strata
program Laurel;
procedure foo() opaque { };
procedure foo() opaque { };
//        ^^^ error: Duplicate definition 'foo' is already defined in this scope
#end

/-! ## Duplicate type names -/

#eval testLaurelExpectResolution <|
#strata
program Laurel;
composite Foo { }
composite Foo { }
//        ^^^ error: Duplicate definition 'Foo' is already defined in this scope
#end

/-! ## Duplicate field names in a composite type -/

#eval testLaurelExpectResolution <|
#strata
program Laurel;
composite Foo {
  var f: int
  var f: bool
//    ^ error: Duplicate definition 'Foo.f' is already defined in this scope
}
#end

/-! ## Duplicate parameter names in a procedure -/

#eval testLaurelExpectResolution <|
#strata
program Laurel;
procedure foo(x: int, x: bool) opaque { };
//                    ^ error: Duplicate definition 'x' is already defined in this scope
#end

/-! ## Duplicate instance procedure names in a composite type -/

#eval testLaurelExpectResolution <|
#strata
program Laurel;
composite Foo {
  procedure bar() opaque { };
  procedure bar() opaque { };
//          ^^^ error: Duplicate definition 'bar' is already defined in this scope
}
#end

/-! ## Duplicate local variable names in the same block -/

#eval testLaurelExpectResolution <|
#strata
program Laurel;
procedure foo() opaque {
  var x: int := 1;
  var x: int := 2
//    ^ error: Duplicate definition 'x' is already defined in this scope
};
#end

/-! ## Procedure and type with the same name -/

#eval testLaurelExpectResolution <|
#strata
program Laurel;
composite Foo { }
procedure Foo() opaque { };
//        ^^^ error: Duplicate definition 'Foo' is already defined in this scope
#end

/-! ## Shadowing quantifier variables in nested scopes is OK (no error expected) -/

/-- info: ok -/
#guard_msgs in
#eval testLaurelResolution
#strata
program Laurel;
procedure test() opaque {
  assert forall(x: int) => forall(x: int) => x > 0
};
#end

/-! ## Shadowing in nested blocks is OK (no error expected) -/

/-- info: ok -/
#guard_msgs in
#eval testLaurelResolution
#strata
program Laurel;
procedure foo() opaque {
  var x: int := 1;
  {
    var x: int := 2
  }
};
#end

/-! ## Duplicate constrained type names -/

#eval testLaurelExpectResolution <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
constrained nat = x: int where x > 0 witness 1
//          ^^^ error: Duplicate definition 'nat' is already defined in this scope
#end

/-! ## Duplicate datatype names -/

#eval testLaurelExpectResolution <|
#strata
program Laurel;
datatype Foo { A }
datatype Foo { B }
//       ^^^ error: Duplicate definition 'Foo' is already defined in this scope
#end

/-! ## Composite type and datatype with the same name -/

#eval testLaurelExpectResolution <|
#strata
program Laurel;
composite Foo { }
datatype Foo { A }
//       ^^^ error: Duplicate definition 'Foo' is already defined in this scope
#end
