/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier
import Strata.Languages.Core
import Strata.MetaVerifier

/-! # Each obligation's query defines only the definitions it reads

A discharge function that reports, per obligation, the variable definitions it is given and the
`define-fun`s of the SMT-LIB file the captured emitter assembled for it. Under `--vcgen wp`,
`a` reads the first definition of `y`, which both arms of the branch read (the definitions read
once are inlined), and `b` reads none, so it is given none of `a`'s. -/

namespace Strata.DefinitionSlicingTest

/-- Two assertions that read disjoint definitions, one of them through a branch. -/
def slicingPgm :=
#strata
program Core;
procedure P(x : int, out y : int)
{
  var u : int := int.add(x, 2);
  y := int.add(x, 1);
  if (int.gt(x, 0)) { y := int.add(y, 1); }
  assert [a]: (int.gt(y, 1));
  assert [b]: (int.gt(u, 1));
};
#end

/-- The names `define-fun` introduces in `text`, in order. -/
def definedFuns (text : String) : List String :=
  (text.splitOn "(define-fun ").drop 1 |>.map fun s => (s.splitOn " ").headD ""

/-- Reports the definitions an obligation is given and those of its captured file, then answers
    `unknown` without running a solver. -/
def reportDefinitions : Core.MkDischargeFn :=
  fun _options _counter _tempDir _vars _md label _termCache captured _pctx =>
    fun _assumptions _obligation _ctx _sat _valid varDefs _varDecls => do
      let file := match captured with
        | some cf => s!"{definedFuns (String.join cf.pieces)}"
        | none => "none"
      IO.println s!"{label}: {varDefs.map (·.name)}, file {file}"
      return .ok (.unknown, .unknown, .init)

/--
info: a: [y@3], file [y@3]
b: [], file []
-/
#guard_msgs in
#eval do
  let _ ← Core.verify slicingPgm (options := { Core.VerifyOptions.quiet with vcgen := .wp })
    (mkDischarge := reportDefinitions)
  pure ()

/-! Slicing leaves out definitions only, never assumptions. The cover `c` reads `x` only, so the
definition of `w` is left out of its query, but the unsatisfiable assumption on `u`, which no
other entry reads, is kept: `c` stays unreachable in both modes, with and without
`--incremental`. -/

/-- A cover after an unsatisfiable assumption on a variable nothing else reads. -/
def deadCoverPgm :=
#strata
program Core;
procedure P(x : int)
{
  var w : int := int.add(x, 1);
  var u : int;
  assume [contradiction]: (int.gt(u, 0) && int.lt(u, 0));
  cover [c]: (int.gt(x, 0));
  assert [a]: (int.gt(w, 0));
};
#end

/--
info: symbolic incremental=false c: unreachable=true
symbolic incremental=true c: unreachable=true
wp incremental=false c: unreachable=true
wp incremental=true c: unreachable=true
-/
#guard_msgs in
#eval do
  for (mode, vcgen) in [("symbolic", Core.VCGenMode.symbolic), ("wp", .wp)] do
    for incremental in [false, true] do
      let options := { Core.VerifyOptions.quiet with vcgen, incremental, checkLevel := .full }
      for r in ← Core.verify deadCoverPgm (options := options) do
        if r.obligation.label == "c" then
          IO.println s!"{mode} incremental={incremental} c: unreachable={r.isUnreachable}"

end Strata.DefinitionSlicingTest
