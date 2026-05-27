/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the resolution pass detects kind mismatches — e.g. using a variable
where a type is expected, or calling a type as if it were a procedure.
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Using a variable name where a type is expected -/

/-- info: 4:9-10  error: 'x' resolves to variable, but expected composite type, constrained type, datatype definition, type alias -/
#guard_msgs in
#eval testLaurelExpectResolution <|
#strata_expect
program Laurel;
procedure foo() opaque {
  var x: int := 1;
  var y: x := 2
};
#end

/-! ## Using a procedure name where a type is expected -/

/-- info: 4:9-12  error: 'bar' resolves to static procedure, but expected composite type, constrained type, datatype definition, type alias -/
#guard_msgs in
#eval testLaurelExpectResolution <|
#strata_expect
program Laurel;
procedure bar() opaque { };
procedure foo() opaque {
  var y: bar := 1
};
#end

/-! ## Calling a composite type as a static call -/

/-- info: 4:16-21  error: 'Foo' resolves to composite type, but expected parameter, static procedure, datatype constructor, datatype destructor, constant -/
#guard_msgs in
#eval testLaurelExpectResolution <|
#strata_expect
program Laurel;
composite Foo { }
procedure bar() opaque {
  var x: int := Foo()
};
#end

/-! ## Using a procedure name with `new` -/

/-- info: 4:16-23  error: 'bar' resolves to static procedure, but expected composite type, datatype definition -/
#guard_msgs in
#eval testLaurelExpectResolution <|
#strata_expect
program Laurel;
procedure bar() opaque { };
procedure foo() opaque {
  var x: int := new bar
};
#end

/-! ## Extending a non-composite type (e.g. a constrained type) -/

/-- info: 3:22-25  error: 'nat' resolves to constrained type, but expected composite type -/
#guard_msgs in
#eval testLaurelExpectResolution <|
#strata_expect
program Laurel;
constrained nat = x: int where x >= 0 witness 0
composite Foo extends nat { }
#end

/-! ## Multi-output procedure used in expression position -/

/-- info: 4:9-17  error: Multi-output procedure 'multi' used in expression position -/
#guard_msgs in
#eval testLaurelExpectResolution <|
#strata_expect
program Laurel;
procedure multi(x: int) returns (a: int, b: int) opaque;
procedure test() opaque {
  assert multi(1) == 1
};
#end
