/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section
open StrataDDM (Program)

---------------------------------------------------------------------
namespace Strata

-- Test that DDM can parse an internal `function` declaration, which translation
-- lowers to a local variable initialized with a `Lambda` abstraction. This test
-- verifies that parsing and type checking work correctly.
def funcDeclStmtPgm : Program :=
#strata
program Core;

procedure testFuncDecl(c: int) {
  function double(x : int) : int { int.add(int.add(x, x), c)}
  var y : int := 5;
  var result : int := double(y);
  assert result == 12;
};

#end

-- Verify the program parses and type checks correctly
/--
info: program Core;
procedure testFuncDecl (c : int)
{
  function double (x : int) : int { int.add(int.add(x, x), c) }
  var y : int := 5;
  var result : int := double(y);
  assert result == 12;
};
-/
#guard_msgs in
#eval IO.println funcDeclStmtPgm

-- Parsing and type checking only; SMT verification of internal functions is
-- not exercised here.
-- #eval verify "z3" funcDeclStmtPgm

---------------------------------------------------------------------

-- Test parsing a top-level block directly (without wrapping in a procedure)
-- This demonstrates the ability to parse statements directly.
def funcDeclBlockPgm : Program :=
#strata
program Core;

{
  var c : int := 2;
  function double(x : int) : int { int.add(int.add(x, x), c) }
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
  function double (x : int) : int { int.add(int.add(x, x), c) }
  var y : int := 5;
  var result : int := double(y);
  assert result == 12;
});
-/
#guard_msgs in
#eval IO.println funcDeclBlockPgm

---------------------------------------------------------------------

end Strata

end
