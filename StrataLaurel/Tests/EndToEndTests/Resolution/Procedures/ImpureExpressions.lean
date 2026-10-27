/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Procedures used by the negative tests below -/

-- Resolution-only errors are reported via the resolution pass; we use the full
-- pipeline helper because the expected diagnostics are not pure resolution
-- errors.

#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure hasMutatingAssignment(): int
  opaque
{
  var x: int := 0;
  x := x + 1;
  x
};

procedure functionCallingHasMutationAssignment(x: int): int
{
  return hasMutatingAssignment()
};

// A call to a procedure with a mutating body is legal in a contract.
procedure impureContractIsLegal1(x: int)
  requires x == hasMutatingAssignment()
  opaque
{
};
#end

/-! ## Destructive assignment in a contract

A destructive assignment in a *contract* is reported by the Core schema
translation, which runs after `FunctionalRewrite`. Since a transparent-body
error there stops the pipeline before the schema pass, this case lives in its own
`#eval` block so it is not masked by the transparent-body diagnostics above.

This check belongs in Laurel resolution. "A contract may not assign" is a property of the
contract's syntax, decidable where the contract is resolved — the sibling cases above, which
reject the same construct in a transparent body, are already reported there. Because this one
is left to the schema pass it reports nothing under `testLaurelResolution` and has to run the
full pipeline. Moving the check into resolution would let it join them.

No interpreters: the schema pass rejects the program, so there is nothing to run — and the
procedure takes a parameter, so there is no parameterless `entry` to mark either. -/

#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure impureContractIsNotLegal2(x: int)
  requires (x := 2) == 2
//          ^^^^^^ error: destructive assignments are not supported in transparent bodies or contracts
  opaque
{
  assert (x := 2) == 2
};
#end

/-! ## Loop in a transparent body

The transparency pass reports only the first fatal transparent-body error per
program, so this case lives in its own `#eval` block to avoid masking (or being
masked by) the destructive-assignment diagnostics above. -/

#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure functionWithWhile(x: int): int
{
  while(false) {};
//^^^^^^^^^^^^^^^ error: loops are not YET supported in transparent bodies or contracts
  return 3
};
#end
