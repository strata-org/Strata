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

/-- info: 3:10-13  error: Duplicate definition 'foo' is already defined in this scope -/
#guard_msgs in
#eval testLaurelExpectResolution <|
#strata_expect
program Laurel;
procedure foo() opaque { };
procedure foo() opaque { };
#end

/-! ## Duplicate type names -/

/-- info: 3:10-13  error: Duplicate definition 'Foo' is already defined in this scope -/
#guard_msgs in
#eval testLaurelExpectResolution <|
#strata_expect
program Laurel;
composite Foo { }
composite Foo { }
#end

/-! ## Duplicate field names in a composite type -/

/-- info: 4:6-7  error: Duplicate definition 'Foo.f' is already defined in this scope -/
#guard_msgs in
#eval testLaurelExpectResolution <|
#strata_expect
program Laurel;
composite Foo {
  var f: int
  var f: bool
}
#end

/-! ## Duplicate parameter names in a procedure -/

/-- info: 2:22-23  error: Duplicate definition 'x' is already defined in this scope -/
#guard_msgs in
#eval testLaurelExpectResolution <|
#strata_expect
program Laurel;
procedure foo(x: int, x: bool) opaque { };
#end

/-! ## Duplicate instance procedure names in a composite type -/

/-- info: 4:12-15  error: Duplicate definition 'bar' is already defined in this scope -/
#guard_msgs in
#eval testLaurelExpectResolution <|
#strata_expect
program Laurel;
composite Foo {
  procedure bar() opaque { };
  procedure bar() opaque { };
}
#end

/-! ## Duplicate local variable names in the same block -/

/-- info: 4:6-7  error: Duplicate definition 'x' is already defined in this scope -/
#guard_msgs in
#eval testLaurelExpectResolution <|
#strata_expect
program Laurel;
procedure foo() opaque {
  var x: int := 1;
  var x: int := 2
};
#end

/-! ## Procedure and type with the same name -/

/-- info: 3:10-13  error: Duplicate definition 'Foo' is already defined in this scope -/
#guard_msgs in
#eval testLaurelExpectResolution <|
#strata_expect
program Laurel;
composite Foo { }
procedure Foo() opaque { };
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

/-- info: 3:12-15  error: Duplicate definition 'nat' is already defined in this scope -/
#guard_msgs in
#eval testLaurelExpectResolution <|
#strata_expect
program Laurel;
constrained nat = x: int where x >= 0 witness 0
constrained nat = x: int where x > 0 witness 1
#end

/-! ## Duplicate datatype names -/

/-- info: 3:9-12  error: Duplicate definition 'Foo' is already defined in this scope -/
#guard_msgs in
#eval testLaurelExpectResolution <|
#strata_expect
program Laurel;
datatype Foo { A }
datatype Foo { B }
#end

/-! ## Composite type and datatype with the same name -/

/-- info: 3:9-12  error: Duplicate definition 'Foo' is already defined in this scope -/
#guard_msgs in
#eval testLaurelExpectResolution <|
#strata_expect
program Laurel;
composite Foo { }
datatype Foo { A }
#end
