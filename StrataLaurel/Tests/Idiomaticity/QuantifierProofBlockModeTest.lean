/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that `TransparencyPass` emits the quantifier proof block only in the
verification modes.

A quantifier whose body carries assert/assume steps is preceded by a proof block:

  var $proof_0: bool;
  if $proof_0 then { var $havoc_0: bool; <body[x := $havoc_0]>; assume false };
  forall(x: bool) => <goal>

The snippets below quantify over `bool` and use the bound variable itself as the
goal, so they contain no operators and resolve without the prelude — which this
test cannot attach, see `printTransparency`.

That scaffolding is verification-only. The nondet `$proof_0` guard is an
uninitialized bool — meaningful to a symbolic verifier, but not to the concrete
interpreter — and the `assume false` seal has nothing to seal under execution. So
`AnalysisMode.Execute` keeps the plain `functionalize` behavior instead.

This is checked at the pass level rather than end-to-end because the interpreter
cannot evaluate a quantified `assert` at all ("condition did not reduce to bool"),
with or without a proof body, so an Execute-mode e2e test would fail for that
unrelated pre-existing reason.
-/

import StrataLaurel.Tests.Util.TestLaurel

open Strata
open StrataTest.Util

namespace Strata.Laurel

/-- Parse, resolve, run `transparencyPass` in the given mode, and print the
    resulting core, so the presence or absence of the quantifier proof scaffolding
    is visible. `prelude := false`: `transparencyPass` derives an `$asFunction`
    copy of every procedure it is given, so the prelude would contribute one per
    operator wrapper. The snippets below therefore use no operators — they quantify
    over `bool` and use the bound variable itself as the goal — so nothing in them
    needs a prelude declaration to resolve. -/
private def printTransparency (mode : AnalysisMode) (program : StrataDDM.Program) : IO Unit :=
  runProgramToCorePassForIdiomaticity transparencyPass program
    (options := { analysisMode := mode }) (prelude := false)

/-! ## Verify mode emits the proof block

    This is the pre-lift shape: the block still sits in the `assert`'s expression
    position, and the later lifting pass hoists its statements out (see
    `LiftExpressionAssignmentsTest.lean`). Note the block's value is the stripped
    quantifier, and no `assume forall(...)` is emitted — the proof block adds the
    body's obligations without establishing the quantifier. -/

/--
info: procedure proofProcedure$asFunction()
  opaque;
procedure proofProcedure()
  opaque
{
  assert {
    var $proof_0: bool;
    if $proof_0
      then {
        var $havoc_0: bool;
        {
          assume $havoc_0;
          $havoc_0
        };
        assume false
      };
    forall(x: bool) => {
      x
    }
  }
};
-/
#guard_msgs in
#eval printTransparency .Verify <|
#strata
program Laurel;
procedure proofProcedure()
  opaque
{
  assert forall(x: bool) => { assume x; x }
};
#end

/-! ## A body with no proof steps gets no proof block, even in Verify mode

    The rewrite is guarded on the body actually containing an `assert`/`assume`.
    A plain goal has no obligations to discharge, so scaffolding it would only add
    a nondet guard and a dead branch. -/

/--
info: procedure plainQuantifier$asFunction()
  opaque;
procedure plainQuantifier()
  opaque
{
  assert forall(x: bool) => x
};
-/
#guard_msgs in
#eval printTransparency .Verify <|
#strata
program Laurel;
procedure plainQuantifier()
  opaque
{
  assert forall(x: bool) => x
};
#end

/-! ## Execute mode does not: the body is simply stripped -/

/--
info: procedure proofProcedure$asFunction()
  opaque;
procedure proofProcedure()
  opaque
{
  assert forall(x: bool) => {
    x
  }
};
-/
#guard_msgs in
#eval printTransparency .Execute <|
#strata
program Laurel;
procedure proofProcedure()
  opaque
{
  assert forall(x: bool) => { assume x; x }
};
#end

/-! ## Nested proof blocks get distinct guard names

    A shared `$proof` would fail Core type checking with "Variable $proof of type
    bool already in context". The counter is handed out as each quantifier is
    *entered*, so the outer block takes `_0` and the one nested in its proof body
    takes `_1`. The inner quantifier's goal is the *outer* bound variable, so the
    golden also shows the nested scaffolding sitting inside the outer havoc's
    scope: it reads `$havoc_0` while binding its own `$havoc_1`. -/

/--
info: procedure nested$asFunction()
  opaque;
procedure nested()
  opaque
{
  assert {
    var $proof_0: bool;
    if $proof_0
      then {
        var $havoc_0: bool;
        {
          assume {
            var $proof_1: bool;
            if $proof_1
              then {
                var $havoc_1: bool;
                {
                  assume $havoc_1;
                  $havoc_0
                };
                assume false
              };
            forall(y: bool) => {
              $havoc_0
            }
          };
          $havoc_0
        };
        assume false
      };
    forall(x: bool) => {
      x
    }
  }
};
-/
#guard_msgs in
#eval printTransparency .Verify <|
#strata
program Laurel;
procedure nested()
  opaque
{
  assert forall(x: bool) => {
    assume forall(y: bool) => { assume y; x };
    x
  }
};
#end

end Laurel
