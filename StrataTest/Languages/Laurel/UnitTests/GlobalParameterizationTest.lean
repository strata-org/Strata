/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Structural tests for global parameterization. Each fixture resolves before and
after lowering; the compact goldens pin threaded signatures and call sites.
-/

import StrataTest.Util.TestLaurel
import Strata.Languages.Laurel.ConstrainedTypeElim
import Strata.Languages.Laurel.GlobalParameterization
import Strata.Languages.Laurel.Resolution

open Strata
open StrataTest.Util

namespace Strata.Laurel

private def testGlobalParam := printGlobalParameterization true

private def testRejectsGlobalConstant (transitive : Bool)
    (program : StrataDDM.Program) : IO Unit := do
  let laurelProgram ← translateLaurel program
  let initializer : StmtExprMd := if transitive then
    ⟨.StaticCall (mkId "readG") [], default⟩
  else
    ⟨.Var (.Local (mkId "g")), default⟩
  let withConstant := { laurelProgram with constants := [{
    name := mkId "globalConstant"
    type := ⟨.TInt, default⟩
    initializer := some initializer
  }] }
  for diagnostic in (resolve (withBuiltins withConstant)).errors do
    IO.println s!"resolution diagnostic: {diagnostic.message}"

private def testConstrainedGlobalShadowing (program : StrataDDM.Program) : IO Unit := do
  let parsed ← translateLaurel program
  let first := resolve (withBuiltins parsed)
  let (unconstrained, constrainedDiagnostics) := constrainedTypeElim first.model first.program
  let second := resolve unconstrained (some first.model)
  let prepared := eliminateValueInReturnsTransform second.program
  let preparedResult := resolve prepared (some second.model)
  let (lowered, loweringDiagnostics, _) :=
    globalParameterizationPass.run {} preparedResult.program preparedResult.model
  let finalResult := resolve lowered (some preparedResult.model)
  for diagnostic in first.errors ++ constrainedDiagnostics ++ second.errors ++
      preparedResult.errors ++ loweringDiagnostics ++ finalResult.errors do
    IO.println s!"diagnostic: {diagnostic.message}"
  for proc in lowered.staticProcedures.filter (·.name.text.startsWith "wrapper") do
    let rendered := toString (Std.Format.pretty
      (formatProgram { staticProcedures := [proc], staticFields := [], types := [] }))
    IO.println (rendered.replace "return \n" "return\n")

private def testDecreasesMetadata (program : StrataDDM.Program) : IO Unit := do
  let laurelProgram ← translateLaurel program
  let measure : StmtExprMd := ⟨.Var (.Field
    ⟨.Var (.Local (mkId "decreasesCell")), default⟩ (mkId "value")), default⟩
  let withDecreases := { laurelProgram with
    staticProcedures := laurelProgram.staticProcedures.map fun proc =>
      if proc.name.text == "measured" then { proc with decreases := some measure }
      else proc }
  let (core, diagnostics, _, _) ← translateWithLaurel {} withDecreases
  IO.println s!"translationErrors: {diagnostics.filter (·.kind != .warning) |>.length}"
  IO.println s!"coreProduced: {core.isSome}"

private def testMetadataTranslation (program : StrataDDM.Program) : IO Unit := do
  let laurelProgram ← translateLaurel program
  let (core, diagnostics, _, _) ← translateWithLaurel {} laurelProgram
  IO.println s!"translationErrors: {diagnostics.filter (·.kind != .warning) |>.length}"
  IO.println s!"coreProduced: {core.isSome}"


private def testConstrainedInvokeOnMetadata (program : StrataDDM.Program) : IO Unit := do
  let laurelProgram ← translateLaurel program
  let parameter : Parameter :=
    { name := mkId "x", type := ⟨.UserDefined (mkId "nat"), default⟩ }
  let xRef : StmtExprMd := ⟨.Var (.Local parameter.name), default⟩
  let gRef : StmtExprMd := ⟨.Var (.Local (mkId "g")), default⟩
  let trigger : StmtExprMd := ⟨.Quantifier .Forall parameter none
    ⟨.StaticCall (mkId Operation.And.procName)
      [⟨.StaticCall (mkId "P") [xRef], default⟩,
       ⟨.StaticCall (mkId Operation.Eq.procName) [gRef, gRef], default⟩], default⟩, default⟩
  let addTrigger (proc : Procedure) :=
    if proc.name.text == "trigger" || proc.name.text == "instanceTrigger" then
      { proc with invokeOn := some trigger }
    else proc
  let withTrigger := { laurelProgram with
    staticProcedures := laurelProgram.staticProcedures.map addTrigger
    types := laurelProgram.types.map fun
      | .Composite composite => .Composite { composite with
          instanceProcedures := composite.instanceProcedures.map addTrigger }
      | other => other }
  let (core, diagnostics, _, _) ← translateWithLaurel {} withTrigger
  IO.println s!"translationErrors: {diagnostics.filter (·.kind != .warning) |>.length}"
  IO.println s!"coreProduced: {core.isSome}"

/-! Readers get inputs; writers get inout parameters. -/

/--
info: staticFields: 0
procedure outer(someGlobal: int)
  returns (someGlobal: int)
{
  someGlobal := writer(someGlobal);
  var x: int := reader(someGlobal)
};
procedure writer(someGlobal: int)
  returns (someGlobal: int)
{
  someGlobal := 3
};
procedure reader(someGlobal: int)
  returns (r: int)
{
  r := someGlobal + 1;
  return
};
-/
#guard_msgs in
#eval testGlobalParam
#strata
program Laurel;
var someGlobal: int := 0
procedure outer() {
  writer();
  var x: int := reader()
};
procedure writer() {
  someGlobal := 3
};
procedure reader() returns (r: int) {
  return someGlobal + 1
};
#end

/-! A writer call in value position yields its original result. -/

/--
info: staticFields: 0
procedure bump(g: int)
  returns (g: int, r: int)
{
  g := g + 1;
  r := g;
  return
};
procedure useValue(g: int)
  returns (g: int, r: int)
{
  r := {
    assign g, var $g_tmp0: int := bump(g);
    $g_tmp0
  } + 1;
  return
};
-/
#guard_msgs in
#eval testGlobalParam
#strata
program Laurel;
var g: int := 0
procedure bump() returns (r: int) {
  g := g + 1;
  return g
};
procedure useValue() returns (r: int) {
  return bump() + 1
};
#end

/-! Globals retain declaration order and per-global framing. -/

/--
info: staticFields: 0
procedure writesA(a: int)
  returns (a: int)
{
  a := 1
};
procedure readsB(b: int)
  returns (r: int)
{
  r := b;
  return
};
procedure both(a: int, b: int)
  returns (a: int, r: int)
{
  a := writesA(a);
  r := readsB(b);
  return
};
-/
#guard_msgs in
#eval testGlobalParam
#strata
program Laurel;
var a: int := 0
var b: int := 0
procedure writesA() {
  a := 1
};
procedure readsB() returns (r: int) {
  return b
};
procedure both() returns (r: int) {
  writesA();
  return readsB()
};
#end

/-! Multiple hidden outputs preserve declaration order for discarded and consumed calls. -/

/--
info: staticFields: 0
procedure writeBoth(a: int, b: int, v: int)
  returns (a: int, b: int, r: int)
{
  a := v;
  b := v + 1;
  r := a + b;
  return
};
procedure useBoth(a: int, b: int)
  returns (a: int, b: int, r: int)
{
  assign a, b, var $g_tmp0: int := writeBoth(a, b, 1);
  r := {
    assign a, b, var $g_tmp1: int := writeBoth(a, b, 2);
    $g_tmp1
  };
  return
};
-/
#guard_msgs in
#eval testGlobalParam
#strata
program Laurel;
var a: int := 0
var b: int := 0
procedure writeBoth(v: int) returns (r: int) {
  a := v;
  b := v + 1;
  return a + b
};
procedure useBoth() returns (r: int) {
  writeBoth(1);
  return writeBoth(2)
};
#end

/-! Explicit assignment to a written global consumes the call's value. -/

/--
info: staticFields: 0
procedure setAndGet(g: int, v: int)
  returns (g: int, r: int)
{
  g := v;
  r := v;
  return
};
procedure useIt(g: int)
  returns (g: int)
  opaque
{
  g := {
    assign g, var $g_tmp0: int := setAndGet(g, 5);
    $g_tmp0
  };
  assert g == 5
};
-/
#guard_msgs in
#eval testGlobalParam
#strata
program Laurel;
var g: int := 0
procedure setAndGet(v: int) returns (r: int) {
  g := v;
  return v
};
procedure useIt() opaque {
  g := setAndGet(5);
  assert g == 5
};
#end

/-! Existing binders keep their names; only the threaded global is renamed. -/

/--
info: staticFields: 0
procedure inc(g: int)
  returns (g: int)
  opaque
{
  g := g + 1
};
procedure withParameter($global_g: int, g: int)
  returns ($global_g: int)
  opaque
{
  $global_g := inc($global_g)
};
procedure withLocal($global_g: int)
  returns ($global_g: int)
  opaque
{
  var g: int := 7;
  $global_g := inc($global_g)
};
-/
#guard_msgs in
#eval testGlobalParam
#strata
program Laurel;
var g: int := 0
procedure inc() opaque {
  g := g + 1
};
procedure withParameter(g: int) opaque {
  inc()
};
procedure withLocal() opaque {
  var g: int := 7;
  inc()
};
#end

/-! Loop bodies and invariants receive the same threaded state. -/

/--
info: staticFields: 0
procedure bump(g: int)
  returns (g: int)
{
  g := g + 1
};
procedure loop(g: int, n: int)
  returns (g: int)
  opaque
{
  var i: int := 0;
  while(i < n)
    invariant i <= n {
    g := bump(g);
    i := i + 1
  }
};
-/
#guard_msgs in
#eval testGlobalParam
#strata
program Laurel;
var g: int := 0
procedure bump() {
  g := g + 1
};
procedure loop(n: int) opaque {
  var i: int := 0;
  while (i < n)
    invariant i <= n {
    bump();
    i := i + 1
  }
};
#end

/-! Assignments in value position preserve the source value. -/

/--
info: staticFields: 0
procedure weird(g: int)
  returns (g: int, r: int)
  opaque
{
  g := 100;
  r := 7;
  return
};
procedure useAssign(g: int)
  returns (g: int, r: int)
  opaque
{
  var x: int := 0;
  r := (x := {
    assign g, var $g_tmp0: int := weird(g);
    $g_tmp0
  }) + 1;
  return
};
-/
#guard_msgs in
#eval testGlobalParam
#strata
program Laurel;
var g: int := 0
procedure weird() returns (r: int) opaque {
  g := 100;
  return 7
};
procedure useAssign() returns (r: int) opaque {
  var x: int := 0;
  return (x := weird()) + 1
};
#end

/-! Effectful explicit arguments finish before hidden globals are sampled. -/

/--
info: staticFields: 0
procedure writeAndReturn(g: int, v: int)
  returns (g: int, r: int)
{
  g := v;
  r := v;
  return
};
procedure readAfter(g: int, x: int)
  returns (r: int)
{
  r := g + x;
  return
};
procedure caller(g: int)
  returns (g: int, r: int)
{
  r := {
    var $g_tmp1: int := {
      assign g, var $g_tmp0: int := writeAndReturn(g, 5);
      $g_tmp0
    };
    readAfter(g, $g_tmp1)
  };
  return
};
-/
#guard_msgs in
#eval testGlobalParam
#strata
program Laurel;
var g: int := 0
procedure writeAndReturn(v: int) returns (r: int) {
  g := v;
  return v
};
procedure readAfter(x: int) returns (r: int) {
  return g + x
};
procedure caller() returns (r: int) {
  return readAfter(writeAndReturn(5))
};
#end

/-! Generated global aliases retry when the first candidate is already bound. -/

/--
info: staticFields: 0
procedure inc(g: int)
  returns (g: int)
  opaque
{
  g := g + 1
};
procedure collides($global_g_1: int, g: int)
  returns ($global_g_1: int)
  opaque
{
  var $global_g: int := 0;
  $global_g_1 := inc($global_g_1)
};
-/
#guard_msgs in
#eval testGlobalParam
#strata
program Laurel;
var g: int := 0
procedure inc() opaque { g := g + 1 };
procedure collides(g: int) opaque {
  var $global_g: int := 0;
  inc()
};
#end

/-! Generated argument temporaries retry around source-local names. -/

/--
info: staticFields: 0
procedure writeAndReturn(g: int, v: int)
  returns (g: int, r: int)
{
  g := v;
  r := v;
  return
};
procedure readAfter(g: int, x: int)
  returns (r: int)
{
  r := g + x;
  return
};
procedure tempCollides(g: int)
  returns (g: int, r: int)
{
  r := {
    var $g_tmp0: int := 0;
    var $g_tmp2: int := {
      assign g, var $g_tmp1: int := writeAndReturn(g, 5);
      $g_tmp1
    };
    readAfter(g, $g_tmp2)
  };
  return
};
-/
#guard_msgs in
#eval testGlobalParam
#strata
program Laurel;
var g: int := 0
procedure writeAndReturn(v: int) returns (r: int) {
  g := v;
  return v
};
procedure readAfter(x: int) returns (r: int) {
  return g + x
};
procedure tempCollides() returns (r: int) {
  return {
    var $g_tmp0: int := 0;
    readAfter(writeAndReturn(5))
  }
};
#end

/-! Recursive writers thread the same inout global through self-calls. -/

/--
info: staticFields: 0
procedure recur(g: int, n: int)
  returns (g: int)
  opaque
{
  if n > 0
    then {
      g := g + 1;
      g := recur(g, n - 1)
    }
};
-/
#guard_msgs in
#eval testGlobalParam
#strata
program Laurel;
var g: int := 0
procedure recur(n: int) opaque {
  if n > 0 then {
    g := g + 1;
    recur(n - 1)
  }
};
#end

private def testDistinctGlobalParameterIds (program : StrataDDM.Program) : IO Unit := do
  let parsed ← translateLaurel program
  let first := resolve (withBuiltins parsed)
  let prepared := eliminateValueInReturnsTransform first.program
  let preparedResult := resolve prepared (some first.model)
  let (lowered, loweringDiagnostics, _) :=
    globalParameterizationPass.run {} preparedResult.program preparedResult.model
  let second := resolve lowered (some preparedResult.model)
  unless first.errors.isEmpty && preparedResult.errors.isEmpty &&
      loweringDiagnostics.isEmpty && second.errors.isEmpty do
    throw (IO.userError "expected global parameterization to produce no diagnostics")
  let ids := second.program.staticProcedures.filterMap fun proc =>
    if proc.name.text == "first" || proc.name.text == "second" then
      proc.inputs.head?.bind (·.name.uniqueId)
    else none
  unless ids.length == 2 && ids.eraseDups.length == 2 do
    throw (IO.userError s!"expected two distinct global parameter IDs, got {ids}")

#guard_msgs in
#eval testDistinctGlobalParameterIds
#strata
program Laurel;
var g: int := 0
procedure first() returns (r: int) { return g };
procedure second() returns (r: int) { return g };
#end

/-! Constant initializers reject direct and transitive global dependencies. -/

/--
info: resolution diagnostic: constant initializer 'globalConstant' cannot depend on file-scope globals
-/
#guard_msgs in
#eval testRejectsGlobalConstant false
#strata
program Laurel;
var g: int := 0
procedure readG() returns (r: int) { return g };
#end

/--
info: resolution diagnostic: constant initializer 'globalConstant' cannot depend on file-scope globals
-/
#guard_msgs in
#eval testRejectsGlobalConstant true
#strata
program Laurel;
var g: int := 0
procedure readG() returns (r: int) { return g };
#end

/-! Generated constrained-global contracts retain global identity across local shadowing. -/

/--
info: procedure wrapperInput($global_g: int, g: int)
  returns (r: int)
  requires nat$constraint($global_g)
  opaque
  ensures nat$constraint(r)
{
  r := readG($global_g);
  return
};
procedure wrapperOutput($global_g: int)
  returns ($global_g: int, g: int)
  requires nat$constraint($global_g)
  opaque
  ensures nat$constraint($global_g)
{
  $global_g := writeG($global_g, 1);
  g := 0
};
-/
#guard_msgs in
#eval testConstrainedGlobalShadowing
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
var g: nat := 0
procedure readG() returns (r: nat) { return g };
procedure writeG(v: nat) { g := v };
procedure wrapperInput(g: int) returns (r: nat) { return readG() };
procedure wrapperOutput() returns (g: int) opaque {
  writeG(1);
  g := 0
};
#end

/-! Global/heap metadata reaches Core without requiring SMT execution. -/

/--
info: translationErrors: 0
coreProduced: true
-/
#guard_msgs in
#eval testMetadataTranslation
#strata
program Laurel;
composite MetadataCell {
  var value: int
}
var c: MetadataCell := new MetadataCell
procedure modifiesGlobal()
  opaque
  modifies c
{
};
procedure P(x: int): bool;
procedure invokesOnGlobalAndHeap()
  invokeOn P(c#value)
  opaque
  ensures true
{
};
#end

/-! Programmatic decreases metadata threads both global and heap state. -/

/--
info: translationErrors: 0
coreProduced: true
-/
#guard_msgs in
#eval testDecreasesMetadata
#strata
program Laurel;
composite DecreasesCell {
  var value: int
}
var decreasesCell: DecreasesCell := new DecreasesCell
procedure measured() opaque {
};
#end

/-! Constrained invokeOn metadata is rewritten for static and instance procedures. -/

/--
info: translationErrors: 0
coreProduced: true
-/
#guard_msgs in
#eval testConstrainedInvokeOnMetadata
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
var g: nat := 0
procedure P(x: int): bool;
procedure trigger() opaque {
};
composite MetadataCell {
  procedure instanceTrigger(self: MetadataCell) opaque {
  };
}
#end

end Strata.Laurel
