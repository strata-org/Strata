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
  function getConstant() : int { 42 }
};

#end

#eval verify "z3" funcDeclStmtPgm

---------------------------------------------------------------------
