/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataTest.Util.TestLaurel

open StrataTest.Util

meta section

#eval testLaurel <|
#strata
program Laurel;

procedure transparentWithMutatingAssignment(x: int): int
{
  x := x + 1;
//^^^^^^^^^^ error: destructive assignments are not supported in transparent bodies or contracts
  return 3
};

procedure impureContractIsNotLegal2(x: int)
  requires (x := 2) == 2
//          ^^^^^^ error: destructive assignments are not supported in transparent bodies or contracts
  opaque
{
  assert (x := 2) == 2
};

#end

end
