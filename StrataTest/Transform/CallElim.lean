/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean
import Strata.DDM.Util.Format
import Strata.Languages.Core.Core
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Languages.Core.ProgramType
import Strata.Languages.Core.ProgramWF
import Strata.Languages.Core.StatementSemantics
import Strata.Transform.CoreTransform
import Strata.Transform.CallElim
import Strata.Languages.Core.Verifier


open Core
open Core.Transform
open CallElim
open Strata

/-! ## Call Elimination Examples -/
section CallElimExamples

def CallElimTest1 :=
#strata
program Core;
procedure f(i : bool, inout j : bool, x : bool, out y : bool)
spec {
  requires (i == !x);
  ensures (y == x);
  ensures (y == j);
};
procedure h(i : bool, inout j : bool, k : bool) {
  var b : bool;
  call f(i, j, k, out j, out b);
};
#end

def CallElimTest1Ans :=
#strata
program Core;
procedure f(i : bool, inout j : bool, x : bool, out y : bool)
spec {
  requires (i == !x);
  ensures (y == x);
  ensures (y == j);
};
procedure h(i : bool, inout j : bool, k : bool) {
  var b : bool;
  var tmp_arg_0 : bool := i;
  var tmp_arg_1 : bool := j;
  var tmp_arg_2 : bool := k;
  var tmp_j_3 : bool := j;
  var tmp_b_4 : bool := b;
  assert [callElimAssert_f_requires_0_5]: (tmp_arg_0 == (!tmp_arg_2));
  havoc j;
  havoc b;
  assume [callElimAssume_f_ensures_1_6]: (b == tmp_arg_2);
  assume [callElimAssume_f_ensures_2_7]: (b == j);
};
#end

def CallElimTest2 :=
#strata
program Core;
procedure f(i : bool, inout j : bool, k : bool, x : bool, y : bool, out z : bool)
spec {
  requires (i == !x);
  ensures (z == (k && old j));
  ensures (z == old j);
};
procedure h(i : bool, inout j : bool, k : bool, l : bool) {
  var b : bool;
  call f(i, j, k, k, l, out j, out b);
};
#end

def CallElimTest2Ans :=
#strata
program Core;
procedure f(i : bool, inout j : bool, k : bool, x : bool, y : bool, out z : bool)
spec {
  requires (i == !x);
  ensures (z == (k && old j));
  ensures (z == old j);
};
procedure h(i : bool, inout j : bool, k : bool, l : bool) {
  var b : bool;
  var tmp_arg_0 : bool := i;
  var tmp_arg_1 : bool := j;
  var tmp_arg_2 : bool := k;
  var tmp_arg_3 : bool := k;
  var tmp_arg_4 : bool := l;
  var tmp_j_5 : bool := j;
  var tmp_b_6 : bool := b;
  var old_j_7 : bool := j;
  assert [callElimAssert_f_requires_0_8]: tmp_arg_0 == !tmp_arg_3;
  havoc j;
  havoc b;
  assume [callElimAssume_f_ensures_1_9]: b == (tmp_arg_2 && old_j_7);
  assume [callElimAssume_f_ensures_2_10]: b == old_j_7;
};
#end

def CallElimTest3 :=
#strata
program Core;
procedure f(i : bool, inout j : bool, k : bool, x : bool, y : bool, out z : bool)
spec {
  requires (i == !x);
  ensures (z == (k && old j));
  ensures (z == old j);
};
procedure h(i : bool, inout j : bool, k : bool, l : bool) {
  var b : bool;
  call f(i, j, k, k && i || j, l, out j, out b);
};
#end

def CallElimTest3Ans :=
#strata
program Core;
procedure f(i : bool, inout j : bool, k : bool, x : bool, y : bool, out z : bool)
spec {
  requires (i == !x);
  ensures (z == (k && old j));
  ensures (z == old j);
};
procedure h(i : bool, inout j : bool, k : bool, l : bool) {
  var b : bool;
  var tmp_arg_0 : bool := i;
  var tmp_arg_1 : bool := j;
  var tmp_arg_2 : bool := k;
  var tmp_arg_3 : bool := k && i || j;
  var tmp_arg_4 : bool := l;
  var tmp_j_5 : bool := j;
  var tmp_b_6 : bool := b;
  var old_j_7 : bool := j;
  assert [callElimAssert_f_requires_0_8]: tmp_arg_0 == !tmp_arg_3;
  havoc j;
  havoc b;
  assume [callElimAssume_f_ensures_1_9]: b == (tmp_arg_2 && old_j_7);
  assume [callElimAssume_f_ensures_2_10]: b == old_j_7;
};
#end

-- Free preconditions should NOT be asserted at call sites
def CallElimTestFreeRequires :=
#strata
program Core;
procedure f(inout j : bool, k : bool, x : bool, out y : bool)
spec {
  free requires (x == k);
  requires (x == j);
  ensures (y == x);
};
procedure h(inout j : bool, k : bool) {
  var b : bool;
  call f(j, k, k, out j, out b);
};
#end

def CallElimTestFreeRequiresAns :=
#strata
program Core;
procedure f(inout j : bool, k : bool, x : bool, out y : bool)
spec {
  free requires (x == k);
  requires (x == j);
  ensures (y == x);
};
procedure h(inout j : bool, k : bool) {
  var b : bool;
  var tmp_arg_0 : bool := j;
  var tmp_arg_1 : bool := k;
  var tmp_arg_2 : bool := k;
  var tmp_j_3 : bool := j;
  var tmp_b_4 : bool := b;
  assert [callElimAssert_f_requires_1_5]: (tmp_arg_2 == tmp_arg_0);
  havoc j;
  havoc b;
  assume [callElimAssume_f_ensures_2_6]: (b == tmp_arg_2);
};
#end

def translate (t : Strata.Program) : Core.Program := (TransM.run Inhabited.default (translateProgram t)).fst

def env : Lambda.LContext CoreLParams := .default (functions := Core.Factory)

def tests : List (Core.Program × Core.Program) := [
  (CallElimTest1, CallElimTest1Ans),
  (CallElimTest2, CallElimTest2Ans),
  (CallElimTest3, CallElimTest3Ans),
  (CallElimTestFreeRequires, CallElimTestFreeRequiresAns),
].map (Prod.map translate translate)

def callElim (p : Core.Program)
  : Core.Program :=
  match (run p callElim') with
  | .ok (_changed, res) => res
  | .error e => panic! e

/--
info: true
-/
#guard_msgs in
#eval tests.all (λ (test, ans) ↦ (toString (callElim test).eraseTypes) == (toString ans.eraseTypes))

end CallElimExamples

/-! ## Call-elimination pipeline phase obligation tests -/
section CallElimPhaseTests
open Strata.SMT
open Core.SMT (Result)

private def satResult : Result := .sat []
private def unknownResult : Result := .unknown (some [])

/-- Obligation with call-elimination labels in path conditions. -/
private def callElimObligation : Imperative.ProofObligation Core.Expression :=
  { label := "test_callElim", property := .assert,
    assumptions := [[("callElimAssume_post", .true ())]],
    obligation := .true (), metadata := {} }

/-- Obligation with no abstraction labels — models are sound. -/
private def cleanObligation : Imperative.ProofObligation Core.Expression :=
  { label := "test_clean", property := .assert,
    assumptions := [[("precond_x_positive", .true ())]],
    obligation := .true (), metadata := {} }

-- callElimPipelinePhase: rejects sat when obligation has call-elim labels
#guard (satResult.adjustForPhases [callElimPipelinePhase.phase] callElimObligation).1 == unknownResult

-- callElimPipelinePhase: preserves sat when obligation has no call-elim labels
#guard (satResult.adjustForPhases [callElimPipelinePhase.phase] cleanObligation).1 == satResult

end CallElimPhaseTests
