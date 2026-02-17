/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def havocPgm : Program :=
#strata
program Core;
procedure S() returns ()
{
  var x : int;
  x := 1;
  havoc x;
  assert [x_eq_1]: (x == 1); // error
};
#end

/-- info: true -/
#guard_msgs in
-- No errors in translation.
#eval TransM.run Inhabited.default (translateProgram havocPgm) |>.snd |>.isEmpty

/--
info: procedure S :  () → ()
  modifies: []
  preconditions: 
  postconditions: 
{
  {
    init (x : int) := some init_x_0
    x := #1
    havoc x
    assert [x_eq_1] ((x : int) == #1)
  }
}
Errors: #[]
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram havocPgm)

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: x_eq_1
Property: assert
Assumptions:


Proof Obligation:
($__x0 == #1)



Obligation x_eq_1: SMT Solver Invocation Error!

Error: stderr:could not execute external process 'cvc5'
 
Ensure cvc5 is on your PATH or use --solver to specify another SMT solver.
solver stdout: {"caption":"","data":"procedure S :  () → ()\n  modifies: []\n  preconditions: \n  postconditions: \n{\n  {\n    init (x : int) := some init_x_0\n    x := #1\n    havoc x\n    assert [x_eq_1] ((x : int) == #1)\n  }\n}\nErrors: #[]","endPos":{"column":5,"line":45},"fileName":"/local/home/mimayere/strata2/StrataTest/Languages/Core/Examples/Havoc.lean","isSilent":false,"keepFullRange":false,"kind":"[anonymous]","pos":{"column":0,"line":45},"severity":"information"}
{"caption":"","data":"❌️ Docstring on `#guard_msgs` does not match generated message:\n\n  info: procedure S :  () → ()\n    modifies: []\n    preconditions: \n    postconditions: \n  {\n    {\n-     init (x : int) := init_x_0\n+     init (x : int) := some init_x_0\n      x := #1\n      havoc x\n      assert [x_eq_1] ((x : int) == #1)\n    }\n  }\n  Errors: #[]\n","endPos":{"column":11,"line":44},"fileName":"/local/home/mimayere/strata2/StrataTest/Languages/Core/Examples/Havoc.lean","isSilent":false,"keepFullRange":false,"kind":"[anonymous]","pos":{"column":0,"line":44},"severity":"error"}



Evaluated program:
procedure S :  () → ()
  modifies: []
  preconditions: 
  postconditions: 
{
  {
    init (x : int) := some init_x_0
    x := #1
    havoc x
    assert [x_eq_1] ($__x0 == #1)
  }
}
---
error: stderr:could not execute external process 'cvc5'
 
Ensure cvc5 is on your PATH or use --solver to specify another SMT solver.
solver stdout: {"caption":"","data":"procedure S :  () → ()\n  modifies: []\n  preconditions: \n  postconditions: \n{\n  {\n    init (x : int) := some init_x_0\n    x := #1\n    havoc x\n    assert [x_eq_1] ((x : int) == #1)\n  }\n}\nErrors: #[]","endPos":{"column":5,"line":45},"fileName":"/local/home/mimayere/strata2/StrataTest/Languages/Core/Examples/Havoc.lean","isSilent":false,"keepFullRange":false,"kind":"[anonymous]","pos":{"column":0,"line":45},"severity":"information"}
{"caption":"","data":"❌️ Docstring on `#guard_msgs` does not match generated message:\n\n  info: procedure S :  () → ()\n    modifies: []\n    preconditions: \n    postconditions: \n  {\n    {\n-     init (x : int) := init_x_0\n+     init (x : int) := some init_x_0\n      x := #1\n      havoc x\n      assert [x_eq_1] ((x : int) == #1)\n    }\n  }\n  Errors: #[]\n","endPos":{"column":11,"line":44},"fileName":"/local/home/mimayere/strata2/StrataTest/Languages/Core/Examples/Havoc.lean","isSilent":false,"keepFullRange":false,"kind":"[anonymous]","pos":{"column":0,"line":44},"severity":"error"}
-/
#guard_msgs in
#eval verify havocPgm

---------------------------------------------------------------------
