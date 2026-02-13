/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier
import Strata.Transform.CallElim

---------------------------------------------------------------------
namespace Strata

private def callElimBugExample : Program :=
#strata
program Core;

procedure Double(n : int) returns (result : int)
spec {
  ensures [double_correct]: (result == n * 2);
}
{
  result := n + n;
};

procedure TestProc(x : int) returns (output : int)
spec {
  ensures [testProc_result]: (output == x * 4);
}
{
  call output := Double(x);      // First call: output = x * 2
  call output := Double(output); // Second call: output = (x * 2) * 2 = x * 4

};
#end

private def testCallElim
    (env : Program)
    (tempDir : Option String := .none)
    : IO Core.VCResults := do
  let (program, errors) := Core.getProgram env Inhabited.default
  if errors.isEmpty then
    match Core.Transform.run program Core.CallElim.callElim' with
    | .error err =>
      panic! s!"Call elimination failed: {err}"
    | .ok (_changed, elimProgram) =>
      dbg_trace f!"New Program:\n{elimProgram}"
      let runner tempDir :=
        EIO.toIO (fun dm => IO.Error.userError (toString (dm.format none)))
                    (Core.verify elimProgram tempDir .none Options.quiet)
      match tempDir with
      | .none =>
        IO.FS.withTempDir runner
      | .some p =>
        IO.FS.createDirAll ⟨p⟩
        runner ⟨p⟩
  else
    panic! s!"DDM Transform Error: {repr errors}"

/--
info: New Program:
procedure Double :  ((n : int)) → ((result : int))
  modifies: []
  preconditions: 
  postconditions: (double_correct, ((result : int) == ((~Int.Mul : (arrow int (arrow int int))) (n : int) #2)))
{
  {
    result := ((~Int.Add : (arrow int (arrow int int))) (n : int) (n : int))
  }
}
procedure TestProc :  ((x : int)) → ((output : int))
  modifies: []
  preconditions: 
  postconditions: (testProc_result, ((output : int) == ((~Int.Mul : (arrow int (arrow int int))) (x : int) #4)))
{
  {
    init (tmp_arg_3 : int) := (x : int)
    init (tmp_output_4 : int) := output
    havoc output
    assume [callElimAssume_double_correct_5] (output == ((~Int.Mul : (arrow int (arrow int int))) tmp_arg_3 #2))
    init (tmp_arg_0 : int) := (output : int)
    init (tmp_output_1 : int) := output
    havoc output
    assume [callElimAssume_double_correct_2] (output == ((~Int.Mul : (arrow int (arrow int int))) tmp_arg_0 #2))
  }
}
---
info:
Obligation: double_correct
Property: assert
Result: ✅ pass

Obligation: testProc_result
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval testCallElim callElimBugExample

---------------------------------------------------------------------

end Strata
