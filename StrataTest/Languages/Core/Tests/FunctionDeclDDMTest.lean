/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

-- Test that DDM can parse function declaration statements
-- Note: SMT verification of locally declared functions is not yet supported
-- (function axioms are not generated for SMT). This test verifies parsing
-- and type checking work correctly.
def funcDeclStmtPgm : Program :=
#strata
program Core;

procedure testFuncDecl(c: int) returns () {
  function double(x : int) : int { x + x + c}
  var y : int := 5;
  var result : int := double(y);
  assert result == 12;
};

#end

-- Verify the program parses and type checks correctly
/--
info: program Core;
procedure testFuncDecl (c : int) returns ()
{
  function double (x : int) : int { x + x + c }
  var y : int := 5;
  var result : int := double(y);
  assert result == 12;
};
-/
#guard_msgs in
#eval IO.println funcDeclStmtPgm

-- SMT verification is not yet supported for locally declared functions
-- #eval verify "z3" funcDeclStmtPgm

---------------------------------------------------------------------

-- Test parsing a top-level block directly (without wrapping in a procedure)
-- This demonstrates the ability to parse statements directly.
def funcDeclBlockPgm : Program :=
#strata
program Core;

{
  var c : int := 2;
  function double(x : int) : int { x + x + c }
  var y : int := 5;
  var result : int := double(y);
  assert result == 12;
};

#end

-- Verify the block program parses and type checks correctly
/--
info: program Core;
({
  var c : int := 2;
  function double (x : int) : int { x + x + c }
  var y : int := 5;
  var result : int := double(y);
  assert result == 12;
});
-/
#guard_msgs in
#eval IO.println funcDeclBlockPgm

---------------------------------------------------------------------
