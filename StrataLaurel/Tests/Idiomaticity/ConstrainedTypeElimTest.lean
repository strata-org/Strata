/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
/-
Tests that the constrained type elimination pass correctly transforms
Laurel programs by comparing the output against expected results.
-/

meta import StrataLaurel.Tests.Util.TestLaurel
import StrataLaurel.Implementation.ConstrainedTypeElim
meta import StrataLaurel.Implementation.Resolution

open Strata
open StrataTest.Util

namespace Strata.Laurel

private meta def parseLaurelAndElim (program : StrataDDM.Program) : IO Program := do
  let laurelProgram ← translateLaurel program
  let result := resolve laurelProgram
  pure (constrainedTypeElim result.model result.program).1

private meta def printElim (program : StrataDDM.Program) : IO Unit := do
  let result ← parseLaurelAndElim program
  for proc in result.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/--
info: procedure nat$constraint(x: int): bool
return x >= 0;
procedure test(n: int)
  returns (r: int)
  requires nat$constraint(n)
  opaque
  ensures nat$constraint(r)
{
  assert r >= 0;
  var y: int := n;
  assert nat$constraint(y);
  return y
};
procedure $witness_nat()
  opaque
{
  var $witness: int := 0;
  assert nat$constraint($witness)
};
-/
#guard_msgs in
#eval printElim <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
procedure test(n: nat) returns (r: nat) opaque {
  assert r >= 0;
  var y: nat := n;
  return y
};
#end

-- Scope management: constrained variable in if-branch must not leak into sibling block
/--
info: procedure pos$constraint(v: int): bool
return v > 0;
procedure test(b: bool)
  opaque
{
  if b
    then {
      var x: int := 1;
      assert pos$constraint(x)
    };
  {
    var x: int := -5;
    x := -10
  }
};
procedure $witness_pos()
  opaque
{
  var $witness: int := 1;
  assert pos$constraint($witness)
};
-/
#guard_msgs in
#eval printElim <|
#strata
program Laurel;
constrained pos = v: int where v > 0 witness 1
procedure test(b: bool) opaque {
  if b then {
    var x: pos := 1
  };
  {
    var x: int := -5;
    x := -10
  }
};
#end

-- Uninitialized constrained variable: havoc + assume constraint.
-- The variable has no known value, only the type constraint is assumed.
/--
info: procedure posint$constraint(x: int): bool
return x > 0;
procedure f()
  opaque
{
  var x: int;
  assume posint$constraint(x);
  assert x == 1
};
procedure $witness_posint()
  opaque
{
  var $witness: int := 1;
  assert posint$constraint($witness)
};
-/
#guard_msgs in
#eval printElim <|
#strata
program Laurel;
constrained posint = x: int where x > 0 witness 1
procedure f() opaque {
  var x: posint;
  assert x == 1
};
#end

-- Composite field of constrained type: field constraint procedure plus the
-- output constraint lemma for the procedure returning the constrained type.
/--
info: procedure nat$constraint(x: int): bool
return x >= 0;
procedure getN(c: Ctr): int
{
  return {
    assume nat$constraint(c#n);
    c#n
  }
};
procedure $witness_nat()
  opaque
{
  var $witness: int := 0;
  assert nat$constraint($witness)
};
procedure $fieldConstraint_Ctr$n($o: Ctr)
  invokeOn $o#n
  opaque
  ensures nat$constraint($o#n);
procedure $constraintLemma_getN(c: Ctr)
  opaque
{
  var $lemma_$result: int := getN(c);
  assert nat$constraint($lemma_$result)
};
-/
#guard_msgs in
#eval printElim <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
composite Ctr { var n: nat }
procedure getN(c: Ctr) : nat { return c#n };
#end

-- Generic procedure: the output constraint lemma must carry the procedure's
-- type arguments.
/--
info: procedure nat$constraint(x: int): bool
return x >= 0;
procedure countOf<T>(x: T): int
{
  return 0
};
procedure $witness_nat()
  opaque
{
  var $witness: int := 0;
  assert nat$constraint($witness)
};
procedure $constraintLemma_countOf<T>(x: T)
  opaque
{
  var $lemma_$result: int := countOf(x);
  assert nat$constraint($lemma_$result)
};
-/
#guard_msgs in
#eval printElim <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
procedure countOf<T>(x: T) : nat { return 0 };
#end

end Laurel
