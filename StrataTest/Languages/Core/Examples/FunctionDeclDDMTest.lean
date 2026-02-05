/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

-- Test that DDM can parse function declaration statements
def funcDeclStmtPgm : Program :=
#strata
program Core;

procedure testFuncDecl() returns () {
  function double(x : int) : int { x + x }
  var y : int := 5;
  var result : int := double(y);
  assert result == 10;
};

#end

#eval verify "z3" funcDeclStmtPgm

---------------------------------------------------------------------
