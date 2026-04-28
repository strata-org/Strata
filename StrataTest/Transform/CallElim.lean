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
var i : bool;
var j : bool;
var k : bool;
procedure f(x : bool) returns (y : bool)
spec {
  requires (i == !x);
  ensures (y == x);
  ensures (y == j);
  modifies j;
};
procedure h() returns () spec {
  modifies j;
} {
  var b : bool;
  call b := f(k);
};
#end

def CallElimTest1Ans :=
#strata
program Core;
var i : bool;
var j : bool;
var k : bool;
procedure f(x : bool) returns (y : bool)
spec {
  requires (i == !x);
  ensures (y == x);
  ensures (y == j);
  modifies j;
};
procedure h() returns () spec {
  modifies j;
} {
  var b : bool;
  var tmp_arg_0 : bool := k;
  var tmp_b_1 : bool := b;
  assert [callElimAssert_f_requires_0_2]: (i == (!tmp_arg_0));
  havoc b;
  havoc j;
  assume [callElimAssume_f_ensures_1_3]: (b == tmp_arg_0);
  assume [callElimAssume_f_ensures_2_4]: (b == j);
};
#end

def CallElimTest2 :=
#strata
program Core;
var i : bool;
var j : bool;
var k : bool;
var l : bool;
procedure f(x : bool, y : bool) returns (z : bool)
spec {
  requires (i == !x);
  ensures (z == (k && old j));
  ensures (z == old j);
  modifies j;
};
procedure h() returns () spec {
  modifies j;
} {
  var b : bool;
  call b := f(k, l);
};
#end

def CallElimTest2Ans :=
#strata
program Core;
var i : bool;
var j : bool;
var k : bool;
var l : bool;
procedure f(x : bool, y : bool) returns (z : bool)
spec {
  requires (i == !x);
  ensures (z == (k && old j));
  ensures (z == old j);
  modifies j;
};
procedure h() returns () spec {
  modifies j;
} {
  var b : bool;
  var tmp_arg_0 : bool := k;
  var tmp_arg_1 : bool := l;
  var tmp_b_2 : bool := b;
  var old_j_3 : bool := j;
  assert [callElimAssert_f_requires_0_4]: i == !tmp_arg_0;
  havoc b;
  havoc j;
  assume [callElimAssume_f_ensures_1_5]: b == (k && old_j_3);
  assume [callElimAssume_f_ensures_2_6]: b == old_j_3;
};
#end

def CallElimTest3 :=
#strata
program Core;
var i : bool;
var j : bool;
var k : bool;
var l : bool;
procedure f(x : bool, y : bool) returns (z : bool)
spec {
  requires (i == !x);
  ensures (z == (k && old j));
  ensures (z == old j);
  modifies j;
};
procedure h() returns () spec {
  modifies j;
} {
  var b : bool;
  call b := f(k && i || j, l);
};
#end

def CallElimTest3Ans :=
#strata
program Core;
var i : bool;
var j : bool;
var k : bool;
var l : bool;
procedure f(x : bool, y : bool) returns (z : bool)
spec {
  requires (i == !x);
  ensures (z == (k && old j));
  ensures (z == old j);
  modifies j;
};
procedure h() returns () spec {
  modifies j;
} {
  var b : bool;
  var tmp_arg_0 : bool := k && i || j;
  var tmp_arg_1 : bool := l;
  var tmp_b_2 : bool := b;
  var old_j_3 : bool := j;
  assert [callElimAssert_f_requires_0_4]: i == !tmp_arg_0;
  havoc b;
  havoc j;
  assume [callElimAssume_f_ensures_1_5]: b == (k && old_j_3);
  assume [callElimAssume_f_ensures_2_6]: b == old_j_3;
};
#end

-- Free preconditions should NOT be asserted at call sites
def CallElimTestFreeRequires :=
#strata
program Core;
var j : bool;
var k : bool;
procedure f(x : bool) returns (y : bool)
spec {
  free requires (x == k);
  requires (x == j);
  ensures (y == x);
  modifies j;
};
procedure h() returns () spec {
  modifies j;
} {
  var b : bool;
  call b := f(k);
};
#end

def CallElimTestFreeRequiresAns :=
#strata
program Core;
var j : bool;
var k : bool;
procedure f(x : bool) returns (y : bool)
spec {
  free requires (x == k);
  requires (x == j);
  ensures (y == x);
  modifies j;
};
procedure h() returns () spec {
  modifies j;
} {
  var b : bool;
  var tmp_arg_0 : bool := k;
  var tmp_b_1 : bool := b;
  assert [callElimAssert_f_requires_1_2]: (tmp_arg_0 == j);
  havoc b;
  havoc j;
  assume [callElimAssume_f_ensures_2_3]: (b == tmp_arg_0);
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
    assumptions := [[("callElimAssume_post", Core.true)]],
    obligation := Core.true, metadata := {} }

/-- Obligation with no abstraction labels — models are sound. -/
private def cleanObligation : Imperative.ProofObligation Core.Expression :=
  { label := "test_clean", property := .assert,
    assumptions := [[("precond_x_positive", Core.true)]],
    obligation := Core.true, metadata := {} }

-- callElimPipelinePhase: rejects sat when obligation has call-elim labels
#guard (satResult.adjustForPhases [callElimPipelinePhase.phase] callElimObligation).1 == unknownResult

-- callElimPipelinePhase: preserves sat when obligation has no call-elim labels
#guard (satResult.adjustForPhases [callElimPipelinePhase.phase] cleanObligation).1 == satResult

end CallElimPhaseTests
