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

#eval testLaurelResolution <|
#strata
program Laurel;
procedure foo() opaque {
  var x: int := 1;
  var y: x := 2
//       ^ error: 'x' resolves to variable, but expected composite type, constrained type, datatype definition, type alias
};
#end

/-! ## Using a procedure name where a type is expected -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure bar() opaque { };
procedure foo() opaque {
  var y: bar := 1
//       ^^^ error: 'bar' resolves to static procedure, but expected composite type, constrained type, datatype definition, type alias
};
#end

/-! ## Calling a composite type as a static call -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Foo { }
procedure bar() opaque {
  var x: int := Foo()
//              ^^^^^ error: 'Foo' resolves to composite type, but expected parameter, static procedure, datatype constructor, datatype destructor, constant
};
#end

/-! ## Using a procedure name with `new` -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure bar() opaque { };
procedure foo() opaque {
  var x: int := new bar
//              ^^^^^^^ error: 'bar' resolves to static procedure, but expected composite type, datatype definition
};
#end

/-! ## Extending a non-composite type (e.g. a constrained type) -/

#eval testLaurelResolution <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
composite Foo extends nat { }
//                    ^^^ error: 'nat' resolves to constrained type, but expected composite type
#end

/-! ## Multi-output procedure used in expression position -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure multi(x: int) returns (a: int, b: int) opaque;
procedure test() opaque {
  assert multi(1) == 1
//       ^^^^^^^^ error: Multi-output procedure 'multi' used in expression position
};
#end
