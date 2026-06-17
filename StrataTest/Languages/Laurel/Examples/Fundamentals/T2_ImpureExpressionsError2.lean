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

procedure transparentWithWhile(x: int): int
{
  while(false) {};
//^^^^^^^^^^^^^^^ error: loops are not supported in transparent bodies or contracts
  return 3
};

#end

end
