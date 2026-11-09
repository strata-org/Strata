/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
/-
Tests that the constrained type elimination pass correctly transforms
Laurel programs by comparing the output against expected results.

Uses `runPassAfterForIdiomaticity`, the shared idiomaticity driver run with
`EliminateValueInReturns` as the predecessor: parse, resolve, eliminate values in
returns, run `constrainedTypeElimPass`, print the result for the `#guard_msgs`
golden. The predecessor is what makes the input the pass expects — it rewrites
`return e` into an assignment to the output followed by a bare `return`, and an
assignment to the output is exactly what the pass checks a constrained output's
constraint on. Without it a `return e` would carry the value past the pass
unchecked (`StmtExpr.Return.value.some` is in the pass's `unsupported` list).
-/

meta import StrataLaurel.Tests.Util.TestLaurel
import StrataLaurel.Implementation.ConstrainedTypeElim
import StrataLaurel.Implementation.EliminateValueInReturns
import StrataLaurel.Implementation.LowerComposite
import StrataLaurel.Implementation.MonomorphizeComposites

open Strata
open StrataTest.Util

namespace Strata.Laurel

private meta def runAfterLowerComposite (program : StrataDDM.Program)
    (monomorphize : Bool := false) : IO Unit := do
  let resolved := resolve (withBuiltins (← translateLaurel program))
  let resolved := if monomorphize then
      resolve (monomorphizeComposites resolved.program resolved.model).1 (some resolved.model)
    else resolved
  let returned := (eliminateValueInReturnsTransform (.Unordered resolved.program)).laurelProgram!
  let some lowered := (lowerComposite resolved.model returned).toOption
    | IO.println "LowerComposite failed"
  let reresolved := resolve lowered (some resolved.model)
  let (out, _, _) := constrainedTypeElimPass.run {} (.Unordered reresolved.program) reresolved.model
  renderProgramForIdiomaticity out.laurelProgram!

/--
info: procedure nat$constraint(x: int): bool
{
  $result := x >= 0;
  return
};
procedure test(n: int)
  returns (r: int)
  requires nat$constraint(n)
  opaque
  ensures nat$constraint(r)
{
  assert r >= 0;
  var y: int := n;
  assert nat$constraint(y);
  r := y;
  assert nat$constraint(r);
  return
};
procedure $witness_nat()
  opaque
{
  var $witness: int := 0;
  assert nat$constraint($witness)
};
-/
#guard_msgs in
#eval runPassAfterForIdiomaticity constrainedTypeElimPass
  (fun p _ => (eliminateValueInReturnsTransform (.Unordered p)).laurelProgram!) <|
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
{
  $result := v > 0;
  return
};
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
#eval runPassAfterForIdiomaticity constrainedTypeElimPass
  (fun p _ => (eliminateValueInReturnsTransform (.Unordered p)).laurelProgram!) <|
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
{
  $result := x > 0;
  return
};
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
#eval runPassAfterForIdiomaticity constrainedTypeElimPass
  (fun p _ => (eliminateValueInReturnsTransform (.Unordered p)).laurelProgram!) <|
#strata
program Laurel;
constrained posint = x: int where x > 0 witness 1
procedure f() opaque {
  var x: posint;
  assert x == 1
};
#end

-- Hole of a constrained type: bound to a fresh local whose constraint is assumed, so the
-- declaration's check holds.
/--
info: procedure posint$constraint(x: int): bool
{
  $result := x > 0;
  return
};
procedure f()
  opaque
{
  var x: int := {
    var $constrainedHole0: int := <?>;
    assume posint$constraint($constrainedHole0);
    $constrainedHole0
  };
  assert posint$constraint(x);
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
#eval runPassAfterForIdiomaticity constrainedTypeElimPass
  (fun p _ => (eliminateValueInReturnsTransform (.Unordered p)).laurelProgram!) <|
#strata
program Laurel;
constrained posint = x: int where x > 0 witness 1
procedure f() opaque {
  var x: posint := <?>;
  assert x == 1
};
#end

-- Composite field of constrained type, after `LowerComposite` as in the pipeline: a
-- field constraint axiom procedure over the heap field's `int` reference, the field
-- read assumed in range, and the output checked where the body assigns it.
/--
info: datatype TypeTag { Ctr_TypeTag }
datatype Composite { MkComposite(ref: int, typeTag: TypeTag) }
$heapfield var Ctr.n: int
procedure nat$constraint(x: int): bool
{
  $result := x >= 0;
  return
};
procedure Ctr$constraint($c: Composite): bool
{
  $result := Composite..typeTag!($c) == Ctr_TypeTag();
  return
};
procedure getN(c: Composite): int
  free requires Ctr$constraint(c)
{
  $result := {
    assume nat$constraint(Composite..ref!(c)#Ctr.n);
    Composite..ref!(c)#Ctr.n
  };
  assert nat$constraint($result);
  return
};
procedure $allocate()
  returns (r: int)external;
procedure $witness_nat()
  opaque
{
  var $witness: int := 0;
  assert nat$constraint($witness)
};
procedure $witness_Ctr()
  opaque
{
  var $witness: Composite := MkComposite(0, Ctr_TypeTag());
  assert Ctr$constraint($witness)
};
procedure $fieldConstraint_Ctr$n($r: int)
  invokeOn $r#Ctr.n
  opaque
  ensures nat$constraint($r#Ctr.n);
procedure downcast$Ctr(p: Composite)
  returns (r: Composite)
  requires Ctr$constraint(p)
{
  r := p
};
-/
#guard_msgs in
#eval runAfterLowerComposite <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
composite Ctr { var n: nat }
procedure getN(c: Ctr) : nat { return c#n };
#end

-- Generic procedure: the output check sits in the polymorphic body, where the
-- procedure's type arguments are already in scope, so it carries none itself.
/--
info: procedure nat$constraint(x: int): bool
{
  $result := x >= 0;
  return
};
procedure countOf<T>(x: T): int
{
  $result := 0;
  assert nat$constraint($result);
  return
};
procedure $witness_nat()
  opaque
{
  var $witness: int := 0;
  assert nat$constraint($witness)
};
-/
#guard_msgs in
#eval runPassAfterForIdiomaticity constrainedTypeElimPass
  (fun p _ => (eliminateValueInReturnsTransform (.Unordered p)).laurelProgram!) <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
procedure countOf<T>(x: T) : nat { return 0 };
#end

-- Transparent body that leaves its constrained output unassigned on a path:
-- the check lands after the body, on the path that falls off its end.
/--
info: procedure nat$constraint(x: int): bool
{
  $result := x >= 0;
  return
};
procedure partial(b: bool)
  returns (r: int)
{
  if b
    then {
      r := 1;
      assert nat$constraint(r)
    };
  assert nat$constraint(r)
};
procedure $witness_nat()
  opaque
{
  var $witness: int := 0;
  assert nat$constraint($witness)
};
-/
#guard_msgs in
#eval runPassAfterForIdiomaticity constrainedTypeElimPass
  (fun p _ => (eliminateValueInReturnsTransform (.Unordered p)).laurelProgram!) <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
procedure partial(b: bool) returns (r: nat) { if b then { r := 1 } };
#end

-- The instantiations of a generic composite, prepared by `MonomorphizeComposites`, store each field
-- in one heap location. A constraint they all have (`n`) gets one axiom, and a field they declare
-- at different types (`v`, of `Box<int8>` and `Box<nat>`, which `toBox` instantiates) none.
/--
info: datatype TypeTag { Box$a1$int8_TypeTag, Box$a1$nat_TypeTag }
datatype Composite { MkComposite(ref: int, typeTag: TypeTag) }
$heapfield var Box$a1$int8.v: int as Box.v
$heapfield var Box$a1$int8.n: int as Box.n
$heapfield var Box$a1$nat.v: int as Box.v
$heapfield var Box$a1$nat.n: int as Box.n
procedure int8$constraint(x: int): bool
{
  $result := x >= -128 && x <= 127;
  return
};
procedure nat$constraint(x: int): bool
{
  $result := x >= 0;
  return
};
procedure Box$a1$int8$constraint($c: Composite): bool
{
  $result := Composite..typeTag!($c) == Box$a1$int8_TypeTag();
  return
};
procedure Box$a1$nat$constraint($c: Composite): bool
{
  $result := Composite..typeTag!($c) == Box$a1$nat_TypeTag();
  return
};
procedure user(m: (TotalMap int int), k: (TotalMap int int))
  opaque
{
  toBox$a1$int8(m);
  toBox$a1$nat(k)
};
procedure toBox$a1$int8(m: (TotalMap int int))
  returns (r: Composite)
  opaque
  free ensures Box$a1$int8$constraint(r)
{
  r := MkComposite($allocate(), Box$a1$int8_TypeTag())
};
procedure toBox$a1$nat(m: (TotalMap int int))
  returns (r: Composite)
  opaque
  free ensures Box$a1$nat$constraint(r)
{
  r := MkComposite($allocate(), Box$a1$nat_TypeTag())
};
procedure $allocate()
  returns (r: int)external;
procedure $witness_int8()
  opaque
{
  var $witness: int := 0;
  assert int8$constraint($witness)
};
procedure $witness_nat()
  opaque
{
  var $witness: int := 0;
  assert nat$constraint($witness)
};
procedure $witness_Box$a1$int8()
  opaque
{
  var $witness: Composite := MkComposite(0, Box$a1$int8_TypeTag());
  assert Box$a1$int8$constraint($witness)
};
procedure $witness_Box$a1$nat()
  opaque
{
  var $witness: Composite := MkComposite(0, Box$a1$nat_TypeTag());
  assert Box$a1$nat$constraint($witness)
};
procedure $fieldConstraint_Box$a1$int8$n($r: int)
  invokeOn $r#Box$a1$int8.n
  opaque
  ensures int8$constraint($r#Box$a1$int8.n);
procedure downcast$Box$a1$int8(p: Composite)
  returns (r: Composite)
  requires Box$a1$int8$constraint(p)
{
  r := p
};
procedure downcast$Box$a1$nat(p: Composite)
  returns (r: Composite)
  requires Box$a1$nat$constraint(p)
{
  r := p
};
-/
#guard_msgs in
#eval (runAfterLowerComposite (monomorphize := true)) <|
#strata
program Laurel;
constrained int8 = x: int where x >= -128 && x <= 127 witness 0
constrained nat = x: int where x >= 0 witness 0
composite Box<T> {
  var v: T
  var n: int8
}
procedure toBox<T>(m: TotalMap int T) returns (r: Box<T>) opaque { r := new Box<T> };
procedure user(m: TotalMap int int8, k: TotalMap int nat) opaque { toBox(m); toBox(k) };
#end

end Laurel
